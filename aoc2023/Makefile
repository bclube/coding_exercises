.DEFAULT_GOAL := run

fmt:
	go fmt ./...

vet: fmt
	go vet ./...

run: vet
	go run ./...

test:
	go test ./...

.PHONY: \
fmt \
run \
test \
vet