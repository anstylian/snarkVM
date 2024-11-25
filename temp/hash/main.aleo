program hash.aleo;

function main:
    hash.keccak256 97u8 into r0 as field;
    hash.keccak256.clean 97u8 into r0 as field;
    output r0 as field.private;
