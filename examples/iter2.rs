use mut_str::StrExt;

fn main() {
    let mut s = Box::<str>::from("Hello, World!");
    print!("{s:?}");

    // Capitalise all the 'l's.
    s.mut_iter()
        .filter(|c| c == &'l')
        .for_each(|c| c.replace('L').unwrap());

    println!(" -> {s:?}");
}

// Test the example (this can be ignored)
#[test]
fn test() {
    main();
}
