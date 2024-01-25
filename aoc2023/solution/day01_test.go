package solution_test

import (
	"aoc2023/solution"
	"context"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestExtractCalibrationValue(t *testing.T) {
	tests := []struct {
		name    string
		line    string
		want    int
		wantErr bool
	}{
		{
			name:    "digits at start and end",
			line:    "123abc456",
			want:    16,
			wantErr: false,
		},
		{
			name:    "digits in the middle",
			line:    "abc123def456ghi",
			want:    16,
			wantErr: false,
		},
		{
			name:    "single digit",
			line:    "abc5def",
			want:    55,
			wantErr: false,
		},
		{
			name:    "no digits",
			line:    "abcdefghi",
			wantErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := solution.ExtractCalibrationValue(context.Background(), tt.line)
			if tt.wantErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
				require.Equal(t, tt.want, got)
			}
		})
	}
}

func TestExtractCalibrationValueV2(t *testing.T) {
	tests := []struct {
		name    string
		line    string
		want    int
		wantErr bool
	}{
		{
			name:    "digits at start and end",
			line:    "123abc456",
			want:    16,
			wantErr: false,
		},
		{
			name:    "digits in the middle",
			line:    "abc123def456ghi",
			want:    16,
			wantErr: false,
		},
		{
			name:    "spelled out digits at start and end",
			line:    "two1nine",
			want:    29,
			wantErr: false,
		},
		{
			name:    "digit first, spelled out digit last",
			line:    "lol7pqrstsixteen",
			want:    76,
			wantErr: false,
		},
		{
			name:    "three overlapping, spelled out digits",
			line:    "zztwoneightzz",
			want:    28,
			wantErr: false,
		},
		{
			name:    "single digit",
			line:    "abc5def",
			want:    55,
			wantErr: false,
		},
		{
			name:    "single spelled out digit",
			line:    "abcfivedef",
			want:    55,
			wantErr: false,
		},
		{
			name:    "no digits",
			line:    "abcdefghi",
			wantErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := solution.ExtractCalibrationValueV2(context.Background(), tt.line)
			if tt.wantErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
				require.Equal(t, tt.want, got)
			}
		})
	}
}
