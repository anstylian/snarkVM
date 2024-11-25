program hash.aleo;

struct FooBar:
    foo as u8;
    bar as u16;

function main:
    cast 5u8 8u16 into r0 as FooBar;
    hash.keccak256 r0 into r1 as field;
    output r1 as field.private;
