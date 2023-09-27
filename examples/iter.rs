use mut_str::StrExt;

fn main() {
    let mut s = Box::<str>::from("oφ⏣🌑");

    // Iterate over the characters printing their length and bytes
    s.ref_iter()
        .for_each(|c| println!("{c:?}\tlength: {}, bytes: {:?}", c.len(), c.as_bytes()));

    // Iterate over each character trying to make them uppercase
    // (Result::ok is being used to ignore the result)
    s.mut_iter().for_each(|c| {
        c.try_make_uppercase().ok();
    });

    println!("\n{s:?}");
}

// Test the example (this can be ignored)
#[test]
fn test() {
    main();
}
