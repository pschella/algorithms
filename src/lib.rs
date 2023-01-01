use std::fmt::Debug;

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

pub fn stable_partition<T>(v: &mut [T], pred: fn(&T) -> bool) -> Result<usize, String>
where
    T: PartialOrd + Copy + Debug,
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

pub fn quicksort<T>(v: &mut [T])
where
    T: PartialOrd + Copy,
{
    if v.len() == 0 {
        return;
    }
    let q = partition(v, v.len() / 2);
    let (v_left, v_right) = v.split_at_mut(q);
    quicksort(v_left);
    quicksort(&mut v_right[1..]);
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

#[cfg(test)]
mod tests {
    use crate::{nth_elment, partition, quicksort, reverse, rotate, stable_partition};
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
    fn test_quicksort() {
        let mut v: Vec<i32> = vec![42, 76, 6, 33, 55, 97, 93, 30, 20, 56, 14, 39, 69, 30, 11];
        quicksort(&mut v);
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

        let q = stable_partition(&mut v, |&item| item.0 < 47).unwrap();

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
}
