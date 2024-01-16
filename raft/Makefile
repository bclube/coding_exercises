build:
	go build ./...

run:
	go run -race ./...

test:
	go test -race ./...

bench:
	go test -bench=. ./...

fuzz:
	go test -race -fuzz=FuzzTestServerAndEventCombinations -fuzztime=2s ./internal/server
	go test -race -fuzz=FuzzTestIdempotentTest -fuzztime=2s ./internal/server
	go test -race -fuzz=FuzzSequenceOfEvents -fuzztime=2s ./internal/server

rmFuzzData:
	rm -rf ./internal/server/testdata/fuzz

refuzz: rmFuzzData fuzz

clean:
	go clean ./...

cover:
	go test ./... -coverprofile=coverage.unit.out
	gocovmerge coverage.*.out > coverage.out
	go tool cover -html=coverage.out -o coverage.html

.PHONY: \
build \
bench \
clean \
cover \
fuzz \
refuzz \
rmFuzzData \
run \
test \