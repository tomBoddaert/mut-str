use mut_str::StrExt;

fn main() {
    let mut s = Box::<str>::from("👋🌍");
    println!("Original string:       {s:?}"); // "👋🌍"

    // Get a mutable reference to the second character
    let world = s.get_char_mut(1).unwrap();
    println!("Original character:    {world:?}"); // '🌍'

    // Replace '🌍' with 'w' and '_' as padding
    // '🌍' is 4 bytes long and 'w' is 1, so 3 '_'s will be added after.
    world.replace_with_pad_char('w', '_').unwrap();
    println!("Replacement character: {world:?}"); // 'w'

    println!("Final string:          {s:?}"); // "👋w___"
}

// Test the example (this can be ignored)
#[test]
fn test() {
    main();
}
