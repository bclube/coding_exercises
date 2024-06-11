default:
	clear
	cargo run

# check
ch:
	cargo check

# release run
rr:
	cargo build --release
	zsh -c 'time ./target/release/aoc2023-rust'

# update dependencies
up:
	cargo update
# This will update the Cargo.lock file to the latest versions of the dependencies

.PHONY: default ch