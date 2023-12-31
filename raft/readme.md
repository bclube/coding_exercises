# Raft consensus algorithm in Go

## Purpose
This is a personal learning exercise. I'm attempting to create a working implementation of the Raft consensus algorithm. This will most likely start out as a rather naive implementation and will hopefully increase in sophistication as it progresses.

This is to be used for learning purposes only and should not be used outside of this context.

## Diagrams
### Server states
``` mermaid
stateDiagram-v2
    Direction LR
    F: Follower

    C: Candidate

    L: Leader

    [*] --> F
    F --> C : <center>Time out\nstart election</center>

    C --> F : <center>Discovers current\nleader or\nnew term</center>
    C --> C : <center>Times out\nnew election</center>
    C --> L : <center>Receives majority\nof votes</center>

    L --> F : <center>Discovers server\nwith higher term</center>
```
## References
[In Search of an Understandable Consensus Algorithm (Extended Version)](https://raft.github.io/raft.pdf)
