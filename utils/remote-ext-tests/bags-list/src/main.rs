// Copyright 2021 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Remote tests for bags-list pallet.

use clap::{Parser, ValueEnum};

#[derive(Clone, Debug, ValueEnum)]
#[value(rename_all = "PascalCase")]
enum Command {
	CheckMigration,
	SanityCheck,
	Snapshot,
}

#[derive(Clone, Debug, ValueEnum)]
#[value(rename_all = "PascalCase")]
enum Runtime {
	Infrablockspace,
	Kusama,
}

#[derive(Parser)]
struct Cli {
	#[arg(long, short, default_value = "wss://kusama-rpc.polkadot.io:443")]
	uri: String,
	#[arg(long, short, ignore_case = true, value_enum, default_value_t = Runtime::Kusama)]
	runtime: Runtime,
	#[arg(long, short, ignore_case = true, value_enum, default_value_t = Command::SanityCheck)]
	command: Command,
	#[arg(long, short)]
	snapshot_limit: Option<usize>,
}

#[tokio::main]
async fn main() {
	let options = Cli::parse();
	sp_tracing::try_init_simple();

	log::info!(
		target: "remote-ext-tests",
		"using runtime {:?} / command: {:?}",
		options.runtime,
		options.command
	);

	use pallet_bags_list_remote_tests::*;
	match options.runtime {
		Runtime::Infrablockspace => sp_core::crypto::set_default_ss58_version(
			infrablockspace_runtime::Runtime as frame_system::Config >
				::SS58Prefix::get().try_into().unwrap(),
		),
		Runtime::Kusama => sp_core::crypto::set_default_ss58_version(
			<kusama_runtime::Runtime as frame_system::Config>::SS58Prefix::get()
				.try_into()
				.unwrap(),
		),
	};

	match (options.runtime, options.command) {
		(Runtime::Kusama, Command::CheckMigration) => {
			use kusama_runtime::{Block, Runtime};
			use kusama_runtime_constants::currency::UNITS;
			migration::execute::<Runtime, Block>(UNITS as u64, "KSM", options.uri.clone()).await;
		},
		(Runtime::Kusama, Command::SanityCheck) => {
			use kusama_runtime::{Block, Runtime};
			use kusama_runtime_constants::currency::UNITS;
			try_state::execute::<Runtime, Block>(UNITS as u64, "KSM", options.uri.clone()).await;
		},
		(Runtime::Kusama, Command::Snapshot) => {
			use kusama_runtime::{Block, Runtime};
			use kusama_runtime_constants::currency::UNITS;
			snapshot::execute::<Runtime, Block>(
				options.snapshot_limit,
				UNITS.try_into().unwrap(),
				options.uri.clone(),
			)
			.await;
		},
		(Runtime::Infrablockspace, Command::CheckMigration) => {
			use infrablockspace_runtime::{Block, Runtime};
			use infrablockspace_runtime_constants::currency::UNITS;
			migration::execute::<Runtime, Block>(UNITS as u64, "DOT", options.uri.clone()).await;
		},
		(Runtime::Infrablockspace, Command::SanityCheck) => {
			use infrablockspace_runtime::{Block, Runtime};
			use infrablockspace_runtime_constants::currency::UNITS;
			try_state::execute::<Runtime, Block>(UNITS as u64, "DOT", options.uri.clone()).await;
		},
		(Runtime::Infrablockspace, Command::Snapshot) => {
			use infrablockspace_runtime::{Block, Runtime};
			use infrablockspace_runtime_constants::currency::UNITS;
			snapshot::execute::<Runtime, Block>(
				options.snapshot_limit,
				UNITS.try_into().unwrap(),
				options.uri.clone(),
			)
			.await;
		},
	}
}
