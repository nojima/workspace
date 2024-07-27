mod leftist_heap;
use leftist_heap::LeftistHeap;

fn main() {
    let mut heap = LeftistHeap::new();

    // push
    for v in [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] {
        heap.push(v)
    }

    // pop_min
    while !heap.is_empty() {
        println!("{:?}", heap.pop_min());
    }
}
