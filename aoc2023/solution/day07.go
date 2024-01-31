package solution

import (
	"aoc2023/common"
	"context"
	"sort"
	"strconv"

	"golang.org/x/sync/errgroup"
)

func SolveDay07(ctx context.Context) (int, error) {
	g, ctx := errgroup.WithContext(ctx)

	lines, lineReader := common.LinesFromFile(ctx, "day07.txt")
	g.Go(lineReader)
	handStream, mapFn := common.MapValues(ctx, lines, parseHand)
	g.Go(mapFn)
	hands := make([]hand, 0, 1000)
	g.Go(common.ForEach(ctx, handStream, func(ctx context.Context, hand hand) error {
		hands = append(hands, hand)
		return nil
	}))
	err := g.Wait()
	if err != nil {
		return 0, err
	}
	sort.Slice(hands, func(i, j int) bool {
		return hands[i].value < hands[j].value
	})
	var result int
	for i, hand := range hands {
		result += hand.bid * (i + 1)
	}

	return result, nil
}

func parseHand(ctx context.Context, line string) (
	hand hand,
	err error,
) {
	hand.bid, _ = strconv.Atoi(line[6:])
	hand.value = calculateValue(line[:5])
	return
}

type handType int

const (
	none handType = iota
	onePair
	twoPairs
	threeOfAKind
	fullHouse
	fourOfAKind
	fiveOfAKind
)

func calculateValue(cards string) int {
	handType := calculateHandType(cards)
	return int(handType)<<20 |
		calcualateCardValue(cards[0])<<16 |
		calcualateCardValue(cards[1])<<12 |
		calcualateCardValue(cards[2])<<8 |
		calcualateCardValue(cards[3])<<4 |
		calcualateCardValue(cards[4])
}

func calcualateCardValue(card byte) int {
	switch card {
	case wildCard:
		return 0
	case 'A':
		return 14
	case 'K':
		return 13
	case 'Q':
		return 12
	case 'T':
		return 10
	default:
		return int(card - '0')
	}
}

const wildCard = 'J'

func calculateHandType(cards string) handType {
	var wildCount uint8
	var maxFrequency uint8
	frequencies := make(map[rune]uint8)
	for _, card := range cards {
		if card == wildCard {
			wildCount++
			continue
		}
		frequencies[card]++
		if frequencies[card] > maxFrequency {
			maxFrequency = frequencies[card]
		}
	}
	switch maxFrequency + wildCount {
	case 5:
		return fiveOfAKind
	case 4:
		return fourOfAKind
	case 3:
		if len(frequencies) == 2 {
			return fullHouse
		}
		return threeOfAKind
	case 2:
		if len(frequencies) == 3 {
			return twoPairs
		}
		return onePair
	case 1:
		return none
	}
	return none
}

type hand struct {
	bid   int
	value int
}
