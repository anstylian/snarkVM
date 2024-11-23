program hash.aleo;

struct FooBar:
    foo as u8;
    bar as u16;

function main:
    cast 5u8 8u16 into r0 as FooBar;
    hash.portable.keccak256 49u8 into r1 as [u8; 32u32];
    output r1 as [u8; 32u32].public;

// function main:
//    cast 5u8 8u16 into r0 as FooBar;
//    hash.portable.keccak256 r0 into r1 as u8;
//    output r1 as u8.public;
