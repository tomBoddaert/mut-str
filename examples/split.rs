use mut_str::StrExt;

fn main() {
    let mut s = Box::<str>::from("Hello, World!");

    // Split at the space (the space will be at the start of `r`)
    let (l, r) = s.char_split_at_mut(6).unwrap();
    println!("{l:?} {r:?}");

    // Replace `l` and `r`. The replacement is returned without padding
    let replacement_l = l.replace_with_pad_left_space("👋,").unwrap();
    let replacement_r = r.replace_with_pad_space(" 🌍!").unwrap();
    println!("{replacement_l:?} {replacement_r:?}");

    println!("{s:?}");
}

// Test the example (this can be ignored)
#[test]
fn test() {
    main();
}
