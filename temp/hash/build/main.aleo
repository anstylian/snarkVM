program hash.aleo;

function main:
    hash.keccak256 49u8 into r0 as group;
    output r0 as group.private;
