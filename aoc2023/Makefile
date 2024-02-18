.DEFAULT_GOAL := run

fmt:
	go fmt ./...

vet: fmt
	go vet ./...

run:
	go run ./...

test:
	go test ./...

.PHONY: \
fmt \
run \
test \
vet