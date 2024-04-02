APP_NAME := aoc2023

.DEFAULT_GOAL := compile-run

$(APP_NAME): $(wildcard ./**/*.go)
	go build -o ./$(APP_NAME) ./main.go

compile-run: $(APP_NAME)
	./$(APP_NAME)

fmt:
	go fmt ./...

vet: fmt
	go vet ./...

run:
	go run ./...

test:
	go test ./...

.PHONY: \
compile-run \
fmt \
run \
test \
vet \