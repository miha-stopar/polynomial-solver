use std::cmp::Ordering;

/// Implementation of the classical data structure k-dimensional tree for
/// multidimensional indexing.
///
/// Entry is the value stored in the leafs. Node data is some data built bottom
/// up the user may store in each branch node to help in the search.
pub struct KDTree<E: Entry, NodeData> {
    num_dimensions: usize,
    root: Node<E, NodeData>,
}

impl<E: Entry, NodeData> KDTree<E, NodeData> {
    pub fn new<T>(
        num_dimensions: usize,
        elems: Vec<E>,
        map: &impl Fn(&E) -> T,
        builder: &impl Fn(T, T) -> (NodeData, T),
    ) -> Self {
        Self {
            num_dimensions,
            root: Node::new(num_dimensions, elems, map, builder),
        }
    }

    /// Insert a new element and update all the node data up to the tree root.
    ///
    /// # Arguments
    ///
    /// * `new_entry` - The new entry to be inserted.
    /// * `builder` - Function that takes a reference to two entries and builds
    ///   the data for the node containing them, and the data to update the
    ///   upper branch.
    /// * `updater` - Takes a mutable reference to the data from the current
    ///   node, the update data from the changed inner branch, and must update
    ///   the node data and produce the update data for the upper node in the
    ///   tree.
    pub fn insert<T>(
        &mut self,
        new_entry: E,
        builder: &impl Fn(&E, &E) -> (NodeData, T),
        updater: &impl Fn(&mut NodeData, T) -> T,
    ) {
        if let Node::Empty = self.root {
            self.root = Node::Entry(new_entry);
        } else {
            self.root
                .insert(&new_entry, self.num_dimensions, 0, builder, updater);
        }
    }

    /// Perform a tree search, where the user must provide the function telling
    /// which branch of the tree to search, and a function to process every
    /// entry found (which returns true if the search must continue, false
    /// otherwise).
    pub fn search(
        &self,
        discriminator: &impl Fn(&E::KeyElem, &NodeData) -> SearchPath,
        processor: &mut impl FnMut(&E) -> bool,
    ) {
        match self.root {
            Node::Empty => (),
            _ => {
                self.root.search(discriminator, processor);
            }
        }
    }
}

/// What side of the branch a search must take.
#[derive(PartialEq, Eq)]
pub enum SearchPath {
    None,
    LessThan,
    GreaterOrEqualThan,
    Both,
}

enum Node<E: Entry, NodeData> {
    Empty,
    Bifurcation {
        split_value: E::KeyElem,
        node_data: NodeData,
        less_branch: Box<Self>,
        greater_or_equal_branch: Box<Self>,
    },
    Entry(E),
}

impl<E: Entry, NodeData> Node<E, NodeData> {
    fn new<T>(
        num_dimensions: usize,
        elems: Vec<E>,
        map: &impl Fn(&E) -> T,
        builder: &impl Fn(T, T) -> (NodeData, T),
    ) -> Self {
        if elems.is_empty() {
            return Self::Empty;
        }

        // Sort the elements by each dimension of the key vector.
        let mut sorted_by_dim = Vec::new();
        sorted_by_dim.resize(num_dimensions, elems);
        for (idx, s) in sorted_by_dim.iter_mut().enumerate() {
            s.sort_unstable_by(|a, b| a.cmp_dim(&b.get_key_elem(idx)));
        }

        // Recursively build the tree.
        let sorted_by_dim: Vec<(usize, &mut [E])> = sorted_by_dim
            .iter_mut()
            .enumerate()
            .map(|(dim, v)| (dim, &mut v[..]))
            .collect();
        Self::build_tree(sorted_by_dim, map, builder).0
    }

    /// Gets the set of elements to be inserted on the list sorted by each one
    /// of the key dimension and build the tree.
    fn build_tree<T>(
        sorted_by_dim: Vec<(usize, &mut [E])>,
        map: &impl Fn(&E) -> T,
        builder: &impl Fn(T, T) -> (NodeData, T),
    ) -> (Self, T) {
        let mut iter = sorted_by_dim.into_iter();
        let (dim, working_list) = iter.next().unwrap();

        // Handle leaf case
        if working_list.len() == 1 {
            let entry = working_list[0];
            return (Node::Entry(entry), map(&entry));
        }

        // Maybe eliminate this dimension if the elements are all equal on it.
        if working_list
            .first()
            .unwrap()
            .cmp_dim(&working_list.last().unwrap().get_key_elem(dim))
            == Ordering::Equal
        {
            // All the elements have the same key on this dimension, so there is
            // no point indexing by it. Recurse with only the other dimensions.
            return Self::build_tree(iter.collect(), map, builder);
        }

        // Find the splitting point. Start from the middle
        // and search for the splitting point that best balance
        // both sides of the tree.
        let middle = working_list.len() / 2;
        let middle_elem = working_list[middle].get_key_elem(dim);

        // The default value for split_idx is for when there is an odd number of
        // elements, and all the elements are equal except for the last.
        let mut split_idx = working_list.len() - 1;
        for (low, high) in (0..middle).rev().zip(middle..) {
            match working_list[low].cmp_dim(&middle_elem) {
                Ordering::Less => {
                    split_idx = low + 1;
                    break;
                }
                Ordering::Equal => {}
                Ordering::Greater => unreachable!(),
            }

            match working_list[high].cmp_dim(&middle_elem) {
                Ordering::Less => unreachable!(),
                Ordering::Equal => {}
                Ordering::Greater => {
                    split_idx = high;
                    break;
                }
            }
        }
        drop(middle_elem);

        let split_value = working_list[split_idx].get_key_elem(dim);
        assert!(
            working_list[split_idx - 1].cmp_dim(&split_value) == Ordering::Less,
            "bug: k-d tree splitting point is at the wrong place"
        );

        // Stable partition each sorted list by split_value
        let (mut less, mut greater_or_equal): (Vec<_>, Vec<_>) = iter
            .map(|(sorted_dim, sorted_list)| {
                let (less, greater_or_equal) =
                    stable_partition(sorted_list, |e| e.cmp_dim(&split_value) == Ordering::Less);
                assert!(less.len() == split_idx);
                ((sorted_dim, less), (sorted_dim, greater_or_equal))
            })
            .unzip();

        // Insert current dimension split at the end, so to be thes last to be
        // processed again.
        let (l, ge) = working_list.split_at_mut(split_idx);
        less.push((dim, l));
        greater_or_equal.push((dim, ge));

        let (l_branch, l_data) = Self::build_tree(less, map, builder);
        let (ge_branch, ge_data) = Self::build_tree(greater_or_equal, map, builder);
        let (node_data, ret_data) = builder(l_data, ge_data);

        (
            Node::Bifurcation {
                split_value,
                less_branch: Box::new(l_branch),
                greater_or_equal_branch: Box::new(ge_branch),
                node_data,
            },
            ret_data,
        )
    }

    fn insert<T>(
        &mut self,
        new_elem: &E,
        num_dimensions: usize,
        last_dim: usize,
        builder: &impl Fn(&E, &E) -> (NodeData, T),
        updater: &impl Fn(&mut NodeData, T) -> T,
    ) -> T {
        match self {
            Node::Empty => unreachable!(),
            Node::Bifurcation {
                split_value,
                less_branch,
                greater_or_equal_branch,
                node_data,
            } => {
                let path = match new_elem.cmp_dim(split_value) {
                    Ordering::Less => less_branch,
                    Ordering::Equal => greater_or_equal_branch,
                    Ordering::Greater => greater_or_equal_branch,
                };
                let update_data = path.insert(
                    new_elem,
                    num_dimensions,
                    split_value.dim_index(),
                    builder,
                    updater,
                );

                updater(node_data, update_data)
            }
            Node::Entry(existing_elem) => {
                for i in 0..num_dimensions {
                    let dim = (i + last_dim) % num_dimensions;
                    let (l, ge): (&E, &E) = match existing_elem.cmp_dim(&new_elem.get_key_elem(dim))
                    {
                        Ordering::Less => (existing_elem, new_elem),
                        Ordering::Greater => (new_elem, existing_elem),
                        Ordering::Equal => {
                            // Can't distinguish the elements by this dimension.
                            continue;
                        }
                    };

                    let (node_data, ret) = builder(l, ge);

                    *self = Node::Bifurcation {
                        split_value: l.average_key_elem(ge, dim),
                        less_branch: Box::new(Node::Entry(*l)),
                        greater_or_equal_branch: Box::new(Node::Entry(*ge)),
                        node_data,
                    };
                    return ret;
                }
                panic!("this k-d tree implementation does not support repeated elements");
            }
        }
    }

    fn search(
        &self,
        discriminator: &impl Fn(&E::KeyElem, &NodeData) -> SearchPath,
        processor: &mut impl FnMut(&E) -> bool,
    ) -> bool {
        match self {
            Node::Empty => unreachable!(),
            Node::Bifurcation {
                split_value,
                less_branch,
                greater_or_equal_branch,
                node_data,
            } => match discriminator(split_value, node_data) {
                SearchPath::None => true,
                SearchPath::LessThan => less_branch.search(discriminator, processor),
                SearchPath::GreaterOrEqualThan => {
                    greater_or_equal_branch.search(discriminator, processor)
                }
                SearchPath::Both => {
                    less_branch.search(discriminator, processor)
                        && greater_or_equal_branch.search(discriminator, processor)
                }
            },
            Node::Entry(e) => processor(e),
        }
    }
}

/// Partition a slice in two according to a predicate, preserving the relative
/// order. Returns two slices, the first with the elements matching the
/// predicate, and the second with the elements not matching.
fn stable_partition<T: Copy, P: Fn(&T) -> bool>(
    list: &mut [T],
    predicate: P,
) -> (&mut [T], &mut [T]) {
    let mut tmp = Vec::new();

    let mut src = 0;
    let mut dst = 0;
    while src < list.len() {
        if predicate(&list[src]) {
            list[dst] = list[src];
            dst += 1;
        } else {
            tmp.push(list[src]);
        }
        src += 1;
    }

    let (matching, unmatching) = list.split_at_mut(list.len() - tmp.len());
    unmatching.copy_from_slice(&tmp[..]);

    (matching, unmatching)
}

/// A k-dimensional vector entry for the k-dimensional tree.
///
/// This will be copied a lot, so make sure it is a small object.
pub trait Entry: Copy {
    type KeyElem: KeyElem;

    fn get_key_elem(&self, dim: usize) -> Self::KeyElem;

    /// Returns a key element in dimension dim in the range defined by
    /// (self, other], i.e. at dimension dim it must be greater than self
    /// and less than or equal other, preferably the average between the two.
    ///
    /// `other.get_key_elem(dim);` is always a valid implementation, but if
    /// averaging is possible between key elements, it will give a slightly more
    /// balanced tree.
    fn average_key_elem(&self, other: &Self, dim: usize) -> Self::KeyElem;

    /// Compares the corresponding key element inside this entry with the
    /// provided key element.
    fn cmp_dim(&self, other: &Self::KeyElem) -> Ordering;
}

/// One element of the k-dimensional key.
pub trait KeyElem {
    /// The index of this key element inside the KDEntry.
    fn dim_index(&self) -> usize;
}

#[cfg(test)]
mod tests {

    use rand::{
        distributions::{Alphanumeric, DistString},
        rngs::StdRng,
        Rng, SeedableRng,
    };

    use super::*;

    /// Defines a 10 dimensional value with 1 string and 9 integers.
    type TestValue = (String, [i8; 9]);

    /// The entry actually inserted is a reference into the value.
    type TestEntry<'a> = &'a TestValue;

    /// The key element is either a pointer to the string or one of the integers.
    pub enum TestKeyElement<'a> {
        Str(&'a str),
        Int { dim: u8, val: i8 },
    }

    type TestKDTree<'a> = KDTree<TestEntry<'a>, ()>;

    impl<'a> Entry for TestEntry<'a> {
        type KeyElem = TestKeyElement<'a>;

        fn get_key_elem(&self, dim: usize) -> Self::KeyElem {
            if dim == 0 {
                TestKeyElement::Str(&self.0)
            } else {
                TestKeyElement::Int {
                    dim: dim as u8,
                    val: self.1[dim - 1],
                }
            }
        }

        fn average_key_elem(&self, other: &Self, dim: usize) -> Self::KeyElem {
            if dim == 0 {
                // Too hard to average two strings, just return the bigger one.
                other.get_key_elem(0)
            } else {
                let lower = self.1[dim - 1];
                let higher = other.1[dim - 1];

                TestKeyElement::Int {
                    dim: dim as u8,
                    val: div_up(lower + higher, 2),
                }
            }
        }

        fn cmp_dim(&self, other: &Self::KeyElem) -> Ordering {
            match other {
                TestKeyElement::Str(other) => self.0.as_str().cmp(other),
                TestKeyElement::Int { dim, val } => self.1[(dim - 1) as usize].cmp(val),
            }
        }
    }

    fn div_up(a: i8, b: i8) -> i8 {
        (a + (b - 1)) / b
    }

    impl<'a> KeyElem for TestKeyElement<'a> {
        fn dim_index(&self) -> usize {
            match self {
                TestKeyElement::Str(_) => 0,
                TestKeyElement::Int { dim, val: _ } => *dim as usize,
            }
        }
    }

    fn rand_string<R: Rng>(rng: &mut R) -> String {
        let size = rng.gen_range(2usize..=10);
        Alphanumeric.sample_string(rng, size)
    }

    #[test]
    fn build_and_query() {
        let mut rng = StdRng::seed_from_u64(42);

        // Generate 10000 elements to be inserted into the k-d tree.
        // Just hope they are distinct for the seed given.
        let mut elem_vec = Vec::new();
        while elem_vec.len() < 10000 {
            let mut new_elem = (rand_string(&mut rng), [0i8; 9]);
            for e in new_elem.1.iter_mut() {
                *e = rng.gen_range(-50..=50);
            }
            elem_vec.push(new_elem);
        }

        // Build the k-d tree with only the first 8000 elements and run the
        // query test.
        let originals = &elem_vec[..8000];
        let mut kdtree = TestKDTree::new(10, originals.iter().collect(), &|_| (), &|_, _| ((), ()));
        query_test(&kdtree, originals);

        // Insert the remaining elements and redo the query test.
        for e in elem_vec[8000..].iter() {
            kdtree.insert(e, &|_, _| ((), ()), &|_, _| ());
        }
        query_test(&kdtree, &elem_vec);
    }

    fn query_test(kdtree: &KDTree<TestEntry, ()>, elems: &[TestValue]) {
        // Search all elements less than or equal the reference:
        let reference: TestValue = ("Q".into(), [-12, 0, -7, 18, 40, -3, -39, 30, 30]);

        let is_less_or_equal = |e: &TestEntry| {
            (0usize..10).all(|dim| e.cmp_dim(&(&reference).get_key_elem(dim)) != Ordering::Greater)
        };

        let mut tree_found = Vec::new();
        kdtree.search(
            &|key, _| match (&reference).cmp_dim(key) {
                Ordering::Less => SearchPath::LessThan,
                Ordering::Equal => SearchPath::Both,
                Ordering::Greater => SearchPath::Both,
            },
            &mut |e| {
                if is_less_or_equal(e) {
                    tree_found.push(*e);
                }
                true
            },
        );
        tree_found.sort();

        // Linearly filter from the total set of elements, for comparison:
        let mut filtered_found: Vec<TestEntry> = elems.iter().filter(is_less_or_equal).collect();
        filtered_found.sort();
        assert!(tree_found == filtered_found);

        for (a, b) in tree_found.iter().zip(filtered_found.iter()) {
            println!("{:?}, {:?}", **a, **b);
        }
        println!("{}, {}", tree_found.len(), filtered_found.len());
    }
}
