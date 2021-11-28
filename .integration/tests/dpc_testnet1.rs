// Copyright (C) 2019-2021 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use std::sync::atomic::AtomicBool;

use snarkvm_dpc::{prelude::*, testnet1::*};
use snarkvm_utilities::{FromBytes, ToBytes};

use chrono::Utc;
use rand::SeedableRng;
use rand_chacha::ChaChaRng;

#[test]
fn test_testnet1_inner_circuit_id_sanity_check() {
    let expected_inner_circuit_id = vec![
        38, 149, 62, 85, 12, 96, 163, 74, 30, 248, 94, 243, 149, 119, 106, 96, 148, 11, 109, 30, 115, 235, 144, 28,
        175, 157, 66, 137, 181, 159, 7, 69, 134, 40, 253, 175, 193, 88, 193, 19, 51, 66, 99, 234, 127, 97, 41, 0,
    ];
    let candidate_inner_circuit_id = <Testnet1 as Network>::inner_circuit_id().to_bytes_le().unwrap();
    assert_eq!(expected_inner_circuit_id, candidate_inner_circuit_id);
}

#[test]
fn dpc_testnet1_integration_test() {
    let mut rng = &mut ChaChaRng::seed_from_u64(1231275789u64);

    let mut ledger = Ledger::<Testnet1>::new().unwrap();
    assert_eq!(ledger.latest_block_height(), 0);
    assert_eq!(ledger.latest_block_hash(), Testnet1::genesis_block().hash());
    assert_eq!(&ledger.latest_block().unwrap(), Testnet1::genesis_block());
    assert_eq!((*ledger.latest_block_transactions().unwrap()).len(), 1);
    assert_eq!(
        ledger.latest_block().unwrap().to_coinbase_transaction().unwrap(),
        (*ledger.latest_block_transactions().unwrap())[0]
    );

    // Construct the previous block hash and new block height.
    let previous_block = ledger.latest_block().unwrap();
    let previous_hash = previous_block.hash();
    let block_height = previous_block.header().height() + 1;
    assert_eq!(block_height, 1);

    // Construct the new block transactions.
    let recipient = Account::new(rng);
    let amount = Block::<Testnet1>::block_reward(block_height);
    let coinbase_transaction = Transaction::<Testnet1>::new_coinbase(recipient.address(), amount, rng).unwrap();
    {
        // Check that the coinbase transaction is serialized and deserialized correctly.
        let transaction_bytes = coinbase_transaction.to_bytes_le().unwrap();
        let recovered_transaction = Transaction::<Testnet1>::read_le(&transaction_bytes[..]).unwrap();
        assert_eq!(coinbase_transaction, recovered_transaction);

        // Check that coinbase record can be decrypted from the transaction.
        let encrypted_record = coinbase_transaction.ciphertexts().next().unwrap();
        let view_key = ViewKey::from_private_key(recipient.private_key());
        let decrypted_record = Record::from_account_view_key(&view_key, encrypted_record).unwrap();
        assert_eq!(decrypted_record.owner(), recipient.address());
        assert_eq!(decrypted_record.value() as i64, Block::<Testnet1>::block_reward(1).0);
    }
    let transactions = Transactions::from(&[coinbase_transaction]).unwrap();
    let transactions_root = transactions.transactions_root();

    let previous_ledger_root = ledger.latest_ledger_root();
    let timestamp = Utc::now().timestamp();
    let difficulty_target = Blocks::<Testnet1>::compute_difficulty_target(
        previous_block.timestamp(),
        previous_block.difficulty_target(),
        timestamp,
    );

    // Construct the new block header.
    let header = BlockHeader::mine(
        block_height,
        timestamp,
        difficulty_target,
        previous_ledger_root,
        transactions_root,
        &AtomicBool::new(false),
        &mut rng,
    )
    .unwrap();

    // Construct the new block.
    let block = Block::from(previous_hash, header, transactions).unwrap();

    ledger.add_next_block(&block).unwrap();
    assert_eq!(ledger.latest_block_height(), 1);
}
