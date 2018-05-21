mod sliding_minimum;
mod bounded_knapsack;

#[cfg(test)]
mod tests {
    use sliding_minimum::sliding_minimum;

    #[test]
    fn test_sliding_minimum() {
        let a = vec![1, 3, 5, 4, 2];
        let k = 3;
        assert_eq!(vec![1, 3, 2], sliding_minimum(&a, k));
    }
}
