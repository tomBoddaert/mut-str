# `mut-str`

A toolkit for working with mutable string slices (`&mut str`), and immutable ones too!

Pretty much all you can do safely in the standard library with mutable string slices is make them lower or upper case.
This package allows for splitting and slicing by character index (rather than byte index), replacing strings and using references to characters.

All functions on string slices are available either at the package root or as methods on the `StrExt` trait.

```sh
cargo add mut-str
```

## Example

``` rust
use mut_str::StrExt;

let mut welcome = Box::<str>::from("Hello, World!");

// Split by character index
let (l, r) = welcome.char_split_at_mut(7).unwrap();
assert_eq!(l, "Hello, ");
assert_eq!(r, "World!");

// Replace string slices
l.replace_with("mut-str").unwrap();
assert_eq!(l, "mut-str");

// Replace with padding
let sub = r.replace_with_pad_left_char("👑!", ' ').unwrap();
assert_eq!(sub, "👑!");
assert_eq!(r, " 👑!");

assert_eq!(&*welcome, "mut-str 👑!");

// Get character references
let crown = welcome.get_char_mut(8).unwrap();
assert_eq!(crown, '👑');

// Mutate characters
crown.replace('🌍').unwrap();
assert_eq!(crown, '🌍');

// Slice by character index
let l = welcome.char_slice_mut(..7).unwrap();
l.replace_with_pad_left_space("👋").unwrap();

assert_eq!(&*welcome, "   👋 🌍!");
```

## Links
[Latest documentation](https://docs.rs/mut-str/latest/mut_str/)  
[Examples](/examples/)

[`mut-str` on crates.io](https://crates.io/crates/mut-str)  
[`mut-str` on GitHub](https://github.com/tomBoddaert/mut-str)

# Features
- `alloc` (enabled by default) adds implementations that require the `alloc` library.
- `std` (enabled by default, requires `alloc`) adds implementations specific to the standard library.

To make this package `no-std` compatible, disable the `std` feature.  
```sh
cargo add mut-str --no-default-features
```
```sh
cargo add mut-str --no-default-features --features=alloc
```

## License

[`mut-str`](https://github.com/tomBoddaert/mut-str) is dual-licensed under either the [Apache License Version 2.0](/LICENSE_Apache-2.0) or [MIT license](/LICENSE_MIT) at your option.
