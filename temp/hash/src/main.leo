// The 'hash' program.
program hash.aleo {
    struct FooBar {
        foo: u8,
        bar: u16,
    }

    // The 'helloworld' main function.
    transition main() -> field {
    /*
        let foobar_item: FooBar = FooBar {
            foo: 5u8,
            bar: 8u16,
        };
        */

//        let foobar_item: u8 = 97u8;
        let foobar: FooBar = FooBar {
            foo: 5u8,
            bar: 8u16,
        };
        return Keccak256::hash_to_field(foobar);
    }
}
