use std::{fmt::Debug, collections::btree_map::IterMut};

const INSERTION_SORT_LIMIT: usize = 15;

pub fn partition<T>(v: &mut [T], k: usize) -> usize
where
    T: PartialOrd + Copy,
{
    let last = v.len() - 1;
    let mut j = 0;
    v.swap(k, last);
    for i in 0..last {
        if v[i] < v[last] {
            v.swap(j, i);
            j += 1;
        }
    }
    v.swap(j, last);
    j
}

pub fn stable_partition<T, F>(v: &mut [T], pred: &F) -> Result<usize, String>
where
    T: PartialOrd + Copy,
    F: Fn(&T) -> bool,
{
    let n = v.len();
    if n == 0 {
        return Ok(0);
    }
    if n == 1 {
        return Ok(if pred(&v[0]) { 1 } else { 0 });
    }
    let m = n / 2;
    let (v_left, v_right) = v.split_at_mut(m);
    let b = stable_partition(v_left, pred)?;
    let e = m + stable_partition(v_right, pred)?;
    let q = rotate(&mut v[b..e], m-b)?;
    Ok(b + q)
}

pub fn nth_elment<T>(v: &mut [T], k: usize) -> Option<T>
where
    T: PartialOrd + Copy,
{
    if v.len() == 0 {
        return None;
    }
    let mut left: usize = 0;
    let mut right: usize = v.len();
    loop {
        if (right - left) == 1 {
            return Some(v[left]);
        }
        let q = left + partition(&mut v[left..right], (right - left) / 2);
        if k == q {
            return Some(v[k]);
        }
        if k < q {
            right = q;
        } else {
            left = q + 1;
        }
    }
}

pub fn sort<T>(v: &mut [T])
where
    T: PartialOrd + Copy,
{
    quicksort(v);
}

/// Sort elements in `v` preserving existing ordering for equal value elements
/// 
/// Uses merge_sort with O(N) extra storage (allocated once, up front), and
/// insertion_sort for small tails.
pub fn stable_sort<T>(v: &mut [T])
where
    T: PartialOrd + Copy + Debug,
{
    let n = v.len();
    if n == 0 || n == 1 {
        return;
    }
    let mut buffer = Vec::<T>::with_capacity(n);
    merge_sort(v, &mut buffer);
}

pub fn reverse<T>(v: &mut [T]) {
    let n = v.len();
    if n <= 1 {
        return;
    }
    let mut i = 0;
    let mut j = n - 1;
    while i < j {
        v.swap(i, j);
        i += 1;
        j -= 1;
    }
}

pub fn rotate<T>(v: &mut [T], l: usize) -> Result<usize, String> {
    let n = v.len();
    if l > n {
        return Err(format!("{} > {}", l, n));
    }
    reverse(&mut v[..l]);
    reverse(&mut v[l..]);
    reverse(v);
    Ok(n - l)
}

pub fn make_heap<T>(v: &mut [T])
where
    T: PartialOrd + Copy,
{
    let n = v.len() / 2;
    for i in (0..n).rev() {
       heapify(v, i); 
    }
}

pub fn is_heap<T>(v: &[T]) -> bool
where
    T: PartialOrd
{
    let n = v.len();
    for i in 0..n {
        let l = left(i);
        let r = right(i);
        if l < n && v[l] < v[i] {
            return false;
        }
        if r < n && v[r] < v[i] {
            return false;
        }
    }
    true
}

pub fn pop_heap<T>(v: &mut [T])
where
    T: PartialOrd + Copy
{
    let n = v.len();
    if n < 2 {
        return;
    }
    v.swap(0, n-1);
    heapify(&mut v[0..n-1], 0);
}

pub fn push_heap<T>(v: &mut [T])
where
    T: PartialOrd + Copy
{
    let mut i = v.len() - 1;
    let mut p = parent(i);
    while p != 0 {
        if v[i] < v[p] {
            v.swap(i, p);
        }
        i -= 1;
        p = parent(i);
    }
}

pub fn heapsort<T>(v: &mut [T])
where
    T: PartialOrd + Copy
{
    let n = v.len();
    let mut tmp = v.to_vec();
    make_heap(&mut tmp);
    for i in 0..n {
        pop_heap(&mut tmp[0..n-i]);
        v[i] = tmp[n-i-1];
    }
}

pub fn lower_bound<T>(v: & [T], value: T) -> usize
where
    T: PartialOrd + Copy,
{
    let mut n = v.len();
    let mut start = 0;
    let mut end = n;

    while n > 0 {
        let mid = start + n / 2;
        if v[mid] < value {
            start = mid + 1;
        } else {
            end = mid;
        }
        n = end - start;
    }
    return start;
}

pub fn unique<T>(v: &mut [T]) -> usize
where
    T: PartialEq + Copy,
{
    let n = v.len();
    if n == 0 {
        return n;
    }

    let mut i: usize = 1;
    let mut j: usize = 0;
    while i != n {
        if v[j] != v[i] {
            j += 1;
            if j != i {
                v[j] = v[i];
            }
        }
        i += 1;
    }
    j += 1;
    return j;
}

fn heapify<T>(v: &mut [T], i: usize)
where
    T: PartialOrd + Copy,
{
    let l = left(i);
    let r = right(i);
    let n = v.len();
    let mut smallest = i;
    if l < n && v[l] < v[i] {
        smallest = l;
    }
    if r < n && v[r] < v[smallest] {
        smallest = r;
    }
    if smallest != i {
        v.swap(i, smallest);
        heapify(v, smallest);
    }
}

fn parent(i: usize) -> usize {
    (i - 1) / 2
}

fn left(i: usize) -> usize {
    2 * i + 1
}

fn right(i: usize) -> usize {
    2 * i + 2
}

fn insertion_sort<T>(v: &mut [T])
where
    T: PartialOrd + Copy
{
    let n = v.len();
    for i in 0..n {
        let mut j = i;
        while j > 0 && v[j-1] > v[j] {
            v.swap(j-1, j);
            j -= 1;
        }
    }
}

fn quicksort<T>(v: &mut [T])
where
    T: PartialOrd + Copy,
{
    let n = v.len();
    if n == 0 || n == 1 {
        return;
    }
    if n < INSERTION_SORT_LIMIT {
        insertion_sort(v);
        return;
    }
    let q = partition(v, v.len() / 2);
    let (v_left, v_right) = v.split_at_mut(q);
    quicksort(v_left);
    quicksort(&mut v_right[1..]);
}

fn merge_sort<T>(v: &mut [T], buffer: &mut Vec<T>)
where
    T: PartialOrd + Copy + Debug,
{
    let n = v.len();
    if n == 0 || n == 1 {
        return;
    }
    if n < INSERTION_SORT_LIMIT {
        insertion_sort(v);
        return;
    }
    let (v_left, v_right) = v.split_at_mut(n / 2);
    merge_sort(v_left, buffer);
    merge_sort(v_right, buffer);

    // merge
    buffer.clear();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < v_left.len() && j < v_right.len() {
        if v_left[i] <= v_right[j] {
            buffer.push(v_left[i]);
            i += 1;
        } else {
            buffer.push(v_right[j]);
            j += 1;
        }
    }
    while i < v_left.len() {
        buffer.push(v_left[i]);
        i += 1;
    }
    while j < v_right.len() {
        buffer.push(v_right[j]);
        j += 1;
    }
    v.copy_from_slice(&buffer[..]);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_partition() {
        let mut v: Vec<i32> = vec![42, 76, 6, 33, 55, 97, 93, 30, 20, 56, 14, 39, 69, 30, 11];
        let k = v.len() / 2;
        let q = partition(&mut v, k);
        for i in 0..q {
            assert!(v[i] <= v[q]);
        }
        for i in q..(v.len()) {
            assert!(v[i] >= v[q]);
        }
    }

    #[test]
    fn test_nth_element() {
        let mut v: Vec<i32> = vec![42, 76, 6, 33, 55, 97, 93, 30, 20, 56, 14, 39, 69, 30, 11];
        let k = v.len() / 2;
        assert!(nth_elment(&mut v, k) == Some(39));

        for i in 0..k {
            assert!(v[i] <= v[k]);
        }
        for i in k..(v.len()) {
            assert!(v[i] >= v[k]);
        }
    }

    #[test]
    fn test_sort() {
        let mut v: Vec<i32> = vec![42, 76, 6, 33, 55, 97, 93, 30, 20, 56, 14, 39, 69, 30, 11];
        sort(&mut v);
        let mut lhs = v[0];
        for i in 1..v.len() {
            let rhs = v[i];
            assert!(lhs <= rhs);
            lhs = rhs;
        }
    }

    #[test]
    fn test_reverse() {
        let mut v: Vec<i32> = vec![42, 76, 6, 33, 55, 97, 93, 30, 20, 56, 14, 39, 69, 30, 11];
        let tmp: Vec<i32> = v.clone();
        reverse(&mut v);
        let n = v.len();
        for i in 0..n {
            let j = (n - 1) - i;
            assert!(v[i] == tmp[j]);
        }
    }

    #[test]
    fn test_rotate() {
        let mut v: Vec<i32> = vec![42, 76, 6, 33, 55, 97, 93, 30, 20, 56, 14, 39, 69, 30, 11];
        let expected: Vec<i32> = vec![30, 20, 56, 14, 39, 69, 30, 11, 42, 76, 6, 33, 55, 97, 93];

        let q = rotate(&mut v, 7).expect("something went wrong");
        assert!(q == 8);

        for i in 0..v.len() {
            assert!(v[i] == expected[i]);
        }
    }

    #[derive(Copy, Clone, Debug)]
    struct Pair(i32, i32);

    use std::cmp::Ordering;

    impl PartialEq for Pair {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    impl PartialOrd for Pair {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.0.cmp(&other.0))
        }
    }

    impl Eq for Pair {}

    impl Ord for Pair {
        fn cmp(&self, other: &Self) -> Ordering {
            self.0.cmp(&other.0)
        }
    }

    #[test]
    fn test_stable_partition() {
        let mut v: Vec<Pair> = vec![
            Pair(25, 0),
            Pair(2, 1),
            Pair(48, 2),
            Pair(10, 3),
            Pair(83, 4),
            Pair(29, 5),
            Pair(46, 6),
            Pair(48, 7),
            Pair(81, 8),
            Pair(38, 9),
        ];

        let q = stable_partition(&mut v, &|&item| item.0 < 47).unwrap();

        assert!(q == 6);
        // check ordering
        for i in 0..q {
            assert!(v[i].0 <= v[q].0);
        }
        for i in q..(v.len()) {
            assert!(v[i].0 >= v[q].0);
        }
        // check stability (each sub-group should be strictly increasing in the second element of the pair)
        for i in 1..q {
            assert!(v[i-1].1 <= v[i].1);
        }
        for i in (q+1)..(v.len()) {
            assert!(v[i-1].1 <= v[i].1);
        }
    }

    #[test]
    fn test_stable_sort() {
        let mut v: Vec<Pair> = vec![
            Pair(25, 0),
            Pair(2, 1),
            Pair(48, 2),
            Pair(10, 3),
            Pair(83, 4),
            Pair(29, 5),
            Pair(46, 6),
            Pair(48, 7),
            Pair(81, 8),
            Pair(38, 9),
        ];

        stable_sort(&mut v);

        // check ordering
        let mut lhs = v[0];
        for i in 1..v.len() {
            let rhs = v[i];
            assert!(lhs <= rhs);
            lhs = rhs;
        }
        // check stability (each sub-group should be strictly increasing in the second element of the pair)
        for i in 1..v.len() {
            if v[i-1] == v[i] {
                assert!(v[i-1].1 < v[i].1);
            }
        }
    }

    #[test]
    fn test_heapify() {
        let mut v: Vec<u8> = vec![3, 4, 1];
        heapify(&mut v, 0);
        assert!(v[0] == 1);
        assert!(v[1] == 4);
        assert!(v[2] == 3);
    }

    #[test]
    fn test_make_heap() {
        let mut v: Vec<u8> = vec![10, 1, 3, 7, 3, 5, 19, 27, 2, 0, 19, 11];
        assert!(!is_heap(&v));
        make_heap(&mut v);
        assert!(is_heap(&v));
    }

    #[test]
    fn test_pop_heap() {
        let mut v: Vec<u8> = vec![10, 1, 3, 7, 3, 5, 19, 27, 2, 0, 19, 11];
        assert!(!is_heap(&v));
        make_heap(&mut v);
        assert!(is_heap(&v));
        pop_heap(&mut v);
        assert!(v.pop().unwrap() == 0);
        assert!(is_heap(&v));
    }

    #[test]
    fn test_push_heap() {
        let mut v: Vec<u8> = vec![10, 1, 3, 7, 3, 5, 19, 27, 2, 0, 19, 11];
        assert!(!is_heap(&v));
        make_heap(&mut v);
        assert!(is_heap(&v));
        v.push(4);
        assert!(!is_heap(&v));
        push_heap(&mut v);
        assert!(is_heap(&v));
    }

    #[test]
    fn test_heapsort() {
        let mut v: Vec<i32> = vec![42, 76, 6, 33, 55, 97, 93, 30, 20, 56, 14, 39, 69, 30, 11];
        heapsort(&mut v);
        let mut lhs = v[0];
        for i in 1..v.len() {
            let rhs = v[i];
            assert!(lhs <= rhs);
            lhs = rhs;
        }
    }

    #[test]
    fn test_lower_bound() {
        let v: Vec<i32> = vec![0, 1, 2, 3, 7, 9, 10, 11, 12, 14, 18];
        let n = lower_bound(&v, 5);
        assert!(n == 4);
    }

    #[test]
    fn test_unique() {
        let mut v: Vec<i32> = vec![0, 0, 1, 1, 1, 2, 2, 3, 3, 4, 5, 6, 6, 7];
        let n = unique(&mut v);
        v.resize(n, 0);
        assert!(v == vec![0, 1, 2, 3, 4, 5, 6, 7]);
    }
}
