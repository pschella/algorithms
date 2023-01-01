use algorithms::nth_elment;

fn main() {
    let mut v: Vec<i32> = vec![42, 76, 6, 33, 55, 97, 93, 30, 20, 56, 14, 39, 69, 30, 11];
    let k = v.len() / 2;
    let median = nth_elment(&mut v, k).unwrap();
    println!("median = {}", median);
}
