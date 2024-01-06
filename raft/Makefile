.PHONY: build
build:
	go build ./...

.PHONY: run
run:
	go run -race ./...

.PHONY: test
test:
	go test -race -fuzztime=10s ./...
	go test -race -fuzz=FuzzTestServerAndEventCombinations -fuzztime=2s ./internal/server
	go test -race -fuzz=FuzzTestIdempotentTest -fuzztime=2s ./internal/server

.PHONY: rmFuzzData
rmFuzzData:
	rm -rf ./internal/server/testdata/fuzz

.PHONY: refuzz
refuzz: rmFuzzData test

.PHONY: clean
clean:
	go clean ./...