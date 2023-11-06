use arrayvec::ArrayVec;
use crate::arrayvec;

/// A B-tree backed interval tree.
#[derive(Debug)]
pub struct Tree<K, V, const B: usize = 8> {
    root: Option<Branch<K, V, B>>,
}

#[derive(Debug)]
struct Branch<K, V, const B: usize> {
    keys: ArrayVec<Interval<K>, B>,
    data: Box<BranchData<K, V, B>>, 
}

#[derive(Debug)]
enum BranchData<K, V, const B: usize> {
    Branch(ArrayVec<Branch<K, V, B>, B>),
    Leaf(ArrayVec<Leaf<K, V, B>, B>),
}

#[derive(Debug)]
struct Leaf<K, V, const B: usize> {
    keys: ArrayVec<Interval<K>, B>,
    data: ArrayVec<V, B>,
}

#[derive(PartialEq, Eq, Debug)]
struct Interval<K> {
    start: K,
    end: K,
}

impl<K, V, const B: usize> Tree<K, V, B>
where
    K: Ord + Clone,
{
    pub fn new() -> Self {
        Self { root: None }
    }

    pub fn insert(&mut self, start: K, end: K, value: V) {
        if self.root.is_none() {
            let root = Branch {
                keys: [(start.clone(), end.clone()).into()].into_iter().collect(),
                data: Box::new(BranchData::Leaf(
                    [Leaf {
                        keys: arrayvec![(start.clone(), end.clone()).into()],
                        data: arrayvec![value],
                    }]
                    .into_iter()
                    .collect(),
                )),
            };
            self.root = Some(root);
        } else {
            let mut root = self.root.take().unwrap();
            if let Some(right) = root.insert(Interval { start, end }, value) {
                let new_root = Branch {
                    keys: arrayvec![root.interval(), right.interval()],
                    data: Box::new(BranchData::Branch(arrayvec![root, right])),
                };
                self.root = Some(new_root);
            } else {
                self.root = Some(root);
            }
        }
    }

    pub fn remove(&mut self, start: &K, end: &K, value: &V) -> Option<(K, K, V)>
    where
        V: Eq,
    {
        let root = self.root.as_mut()?;
        let interval = Interval {
            start: start.clone(),
            end: end.clone(),
        };
        let (interval, value) = root.remove(interval, value)?;
        Some((interval.start, interval.end, value))
    }

    pub fn range<'a>(&'a self, start: &K, end: &K, buf: &mut Vec<(&'a K, &'a K, &'a V)>) {
        if let Some(root) = self.root.as_ref() {
            root.range(start, end, buf);
        }
    }
}

impl<K, V, const B: usize> Branch<K, V, B>
where
    K: Ord + Clone,
{
    fn split(&mut self) -> Self {
        let Self { keys, data } = self;
        match data.as_mut() {
            BranchData::Branch(data) => {
                let mut keys_ = ArrayVec::new();
                let mut data_ = ArrayVec::new();
                for _ in 0..(B / 2) {
                    keys_.push(keys.remove(B / 2));
                    data_.push(data.remove(B / 2));
                }
                Self {
                    keys: keys_,
                    data: Box::new(BranchData::Branch(data_)),
                }
            }
            BranchData::Leaf(data) => {
                let mut keys_ = ArrayVec::new();
                let mut data_ = ArrayVec::new();
                for _ in 0..(B / 2) {
                    keys_.push(keys.remove(B / 2));
                    data_.push(data.remove(B / 2));
                }
                Self {
                    keys: keys_,
                    data: Box::new(BranchData::Leaf(data_)),
                }
            }
        }
    }

    fn start(&self) -> &K {
        debug_assert!(!self.is_empty());
        &self.keys[0].start
    }

    fn end(&self) -> &K {
        debug_assert!(!self.is_empty());
        self.keys.iter().map(|k| &k.end).max().unwrap()
    }

    fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    fn interval(&self) -> Interval<K> {
        Interval {
            start: self.start().clone(),
            end: self.end().clone(),
        }
    }

    fn is_full(&self) -> bool {
        self.keys.is_full()
    }

    #[must_use]
    fn insert_branch(&mut self, index: usize, value: Branch<K, V, B>) -> Option<Self> {
        if self.is_full() {
            let mut right = self.split();
            if index < (B / 2) {
                let _ = self.insert_branch(index, value);
            } else {
                let _ = right.insert_branch(index - B / 2, value);
            }
            Some(right)
        } else {
            let Self { keys, data } = self;
            let BranchData::Branch(data) = data.as_mut() else {
                unreachable!()
            };
            keys.insert(index, value.interval());
            data.insert(index, value);
            None
        }
    }

    #[must_use]
    fn insert_leaf(&mut self, index: usize, value: Leaf<K, V, B>) -> Option<Self> {
        if self.is_full() {
            let mut right = self.split();
            if index < (B / 2) {
                let _ = self.insert_leaf(index, value);
            } else {
                let _ = right.insert_leaf(index - B / 2, value);
            }
            Some(right)
        } else {
            let Self { keys, data } = self;
            let BranchData::Leaf(data) = data.as_mut() else {
                unreachable!()
            };
            keys.insert(index, value.interval());
            data.insert(index, value);
            None
        }
    }

    #[must_use]
    fn insert(&mut self, interval: Interval<K>, value: V) -> Option<Self> {
        let Self { keys, data } = self;
        let index = keys
            .iter()
            .take_while(|k| interval.start > k.start)
            .count()
            .saturating_sub(1);
        match data.as_mut() {
            BranchData::Branch(data) => {
                if let Some(right) = data[index].insert(interval, value) {
                    keys[index] = data[index].interval();
                    return self.insert_branch(index + 1, right);
                } else {
                    keys[index] = data[index].interval();
                }
            }
            BranchData::Leaf(data) => {
                if let Some(right) = data[index].insert(interval, value) {
                    keys[index] = data[index].interval();
                    return self.insert_leaf(index + 1, right);
                } else {
                    keys[index] = data[index].interval();
                }
            }
        }
        None
    }

    fn remove(&mut self, interval: Interval<K>, value: &V) -> Option<(Interval<K>, V)>
    where
        V: Eq,
    {
        let index = self
            .keys
            .iter()
            .position(|k| k.start >= interval.start && k.end <= interval.end)?;
        match self.data.as_mut() {
            BranchData::Branch(branch) => branch[index].remove(interval, value),
            BranchData::Leaf(leaf) => leaf[index].remove(interval, value),
        }
    }

    fn range<'a>(&'a self, start: &K, end: &K, buf: &mut Vec<(&'a K, &'a K, &'a V)>) {
        let Self { keys, data } = self;
        match data.as_ref() {
            BranchData::Branch(data) => {
                for (k, v) in keys.iter().zip(data.iter()) {
                    if &k.end >= start || &k.start <= end {
                        v.range(start, end, buf);
                    }
                }
            }
            BranchData::Leaf(data) => {
                for (k, v) in keys.iter().zip(data.iter()) {
                    if &k.end >= start || &k.start <= end {
                        v.range(start, end, buf);
                    }
                }
            }
        }
    }
}

impl<K, V, const B: usize> Leaf<K, V, B>
where
    K: Ord + Clone,
{
    fn split(&mut self) -> Self {
        let mut keys = ArrayVec::new();
        let mut data = ArrayVec::new();
        for _ in 0..(B / 2) {
            keys.push(self.keys.remove(B / 2));
            data.push(self.data.remove(B / 2));
        }
        Self { keys, data }
    }

    fn start(&self) -> &K {
        debug_assert!(!self.is_empty());
        &self.keys.first().unwrap().start
    }

    fn end(&self) -> &K {
        debug_assert!(!self.is_empty());
        self.keys.iter().map(|k| &k.end).max().unwrap()
    }

    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    fn interval(&self) -> Interval<K> {
        Interval {
            start: self.start().clone(),
            end: self.end().clone(),
        }
    }

    fn insert(&mut self, interval: Interval<K>, value: V) -> Option<Self> {
        if self.data.is_full() {
            let mut right = self.split();
            if &interval.start <= self.start() {
                self.insert(interval, value);
            } else {
                right.insert(interval, value);
            }
            Some(right)
        } else {
            let index = self
                .keys
                .iter()
                .take_while(|k| k.start < interval.start)
                .count();
            self.keys.insert(index, interval);
            self.data.insert(index, value);
            None
        }
    }

    fn remove(&mut self, interval: Interval<K>, value: &V) -> Option<(Interval<K>, V)>
    where
        V: Eq,
    {
        let index = self
            .keys
            .iter()
            .position(|i| i.start == interval.start && i.end == interval.end)?;
        if &self.data[index] == value {
            let interval = self.keys.remove(index);
            let value = self.data.remove(index);
            Some((interval, value))
        } else {
            None
        }
    }

    fn range<'a>(&'a self, start: &K, end: &K, buf: &mut Vec<(&'a K, &'a K, &'a V)>) {
        for (k, v) in self.keys.iter().zip(self.data.iter()) {
            if &k.end >= start || &k.start <= end {
                buf.push((&k.start, &k.end, v))
            }
        }
    }
}

impl<K> From<(K, K)> for Interval<K> {
    fn from(value: (K, K)) -> Self {
        let (start, end) = value;
        Self { start, end }
    }
}

#[macro_export]
macro_rules! arrayvec {
    ($elem:expr; $n:expr) => ({
        ::arrayvec::ArrayVec::from([$elem; $n])
    });
    ($($x:expr),*$(,)*) => ({
        ::arrayvec::ArrayVec::from_iter([$($x,)*])
    })
}

#[cfg(test)]
mod tests {
    use crate::arrayvec;
    use crate::tree::{Leaf, Tree};

    #[test]
    fn split_leaf() {
        let mut left: Leaf<i32, i32, 4> = Leaf {
            keys: arrayvec![(1, 1).into(), (2, 2).into(), (3, 3).into(), (4, 4).into(),],
            data: arrayvec![1, 2, 3, 4],
        };
        let right = left.split();
        assert_eq!(left.keys[0], (1, 1).into());
        assert_eq!(left.keys[1], (2, 2).into());
        assert_eq!(right.keys[0], (3, 3).into());
        assert_eq!(right.keys[1], (4, 4).into());
    }

    #[test]
    fn insert_leaf() {
        let mut leaf: Leaf<i32, i32, 4> = Leaf {
            keys: arrayvec![(4, 5).into()],
            data: arrayvec![0],
        };

        leaf.insert((3, 4).into(), 0);
        leaf.insert((5, 6).into(), 0);
        leaf.insert((1, 6).into(), 0);

        assert_eq!(leaf.keys[0], (1, 6).into());
        assert_eq!(leaf.keys[1], (3, 4).into());
        assert_eq!(leaf.keys[2], (4, 5).into());
        assert_eq!(leaf.keys[3], (5, 6).into());
    }

    #[test]
    fn insertion() {
        let mut tree: Tree<i32, i32, 4> = Tree::new();
        tree.insert(0, 4, 1);
        tree.insert(2, 2, 3);
        tree.insert(4, 8, 4);
        tree.insert(1, 3, 2);
        tree.insert(-10, 10, 8);
        tree.insert(-2, 0, 7);
        tree.insert(6, 6, 6);
        tree.insert(5, 7, 5);
        tree.insert(-20, 20, 9);

        let mut range = vec![];
        tree.range(&-10, &10, &mut range);
        let range = range
            .into_iter()
            .map(|(s, e, v)| (*s, *e, *v))
            .collect::<Vec<_>>();
        assert_eq!(
            range,
            vec![
                (-20, 20, 9),
                (-10, 10, 8),
                (-2, 0, 7),
                (0, 4, 1),
                (1, 3, 2),
                (2, 2, 3),
                (4, 8, 4),
                (5, 7, 5),
                (6, 6, 6),
            ]
        );
    }
}
