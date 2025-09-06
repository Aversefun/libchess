//! Board-related stuff.

use core::ops::{Add, AddAssign, Deref, DerefMut};

use anyhow::{Context, anyhow, bail, ensure};
use bstr::ByteSlice;
use smallvec::SmallVec;

use crate::{Color, Piece, Position, from_decimal_u16};

#[cfg(feature = "alloc")]
use alloc::{
    format,
    string::{String, ToString},
    vec::Vec,
};

#[cfg(test)]
use proptest::prelude::*;
#[cfg(test)]
use proptest_derive::Arbitrary;

use core::fmt::Debug;

/// Convenience constant for the width of a chess board.
pub const BOARD_WIDTH: usize = 8;
/// Convenience constant for the height of a chess board.
pub const BOARD_HEIGHT: usize = 8;

/// A chess board.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(not(feature = "alloc"), derive(Debug))]
pub struct Board(pub [Option<(Piece, Color)>; BOARD_WIDTH * BOARD_HEIGHT]);

#[cfg(test)]
impl Arbitrary for Board {
    type Parameters = ();
    type Strategy = SBoxedStrategy<Self>;

    fn arbitrary_with((): Self::Parameters) -> Self::Strategy {
        any::<[Option<(Piece, Color)>; BOARD_WIDTH * BOARD_HEIGHT]>()
            .prop_map(Board)
            .sboxed()
    }
}

#[cfg(feature = "alloc")]
impl Debug for Board {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(&self.into_fen_board())
    }
}

impl Deref for Board {
    type Target = [Option<(Piece, Color)>; BOARD_WIDTH * BOARD_HEIGHT];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Board {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Default for Board {
    fn default() -> Self {
        Self::EMPTY_BOARD
    }
}

impl Board {
    /// The empty board.
    pub const EMPTY_BOARD: Board = Board([None; BOARD_WIDTH * BOARD_HEIGHT]);

    /// Get the FEN-formatted board for this `Board`.
    #[cfg(feature = "alloc")]
    #[must_use]
    #[expect(clippy::missing_panics_doc, reason = "testedly impossible")]
    pub fn into_fen_board(self) -> String {
        let mut contiguous_empty = 0u8;
        let mut out = String::new();

        let add_empties = |contiguous_empty: &mut u8, out: &mut String| {
            if *contiguous_empty > 0 {
                out.push(char::from_u32(u32::from(*contiguous_empty + b'0')).unwrap());
                *contiguous_empty = 0;
            }
        };

        for (i, piece) in self.0.iter().enumerate() {
            if i.is_multiple_of(8) && i > 0 && i != 64 {
                add_empties(&mut contiguous_empty, &mut out);
                out += "/";
            }
            if let Some((piece, color)) = piece {
                add_empties(&mut contiguous_empty, &mut out);
                let mut ch = match piece {
                    Piece::Pawn => "P".to_string(),
                    _ => piece.to_string(),
                };
                if color.black() {
                    ch = ch.to_lowercase();
                }
                out += &ch;
            } else {
                contiguous_empty += 1;
            }
        }

        add_empties(&mut contiguous_empty, &mut out);

        out
    }
}

/// Which direction(s) can the player castle?
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Arbitrary))]
#[cfg_attr(test, proptest(no_params))]
pub enum Castling {
    /// Neither side.
    Neither,
    /// Just kingside.
    Kingside,
    /// Just queenside.
    Queenside,
    /// Both sides.
    Both,
}

impl Castling {
    /// Can this player castle kingside?
    #[must_use]
    pub fn kingside(self) -> bool {
        matches!(self, Castling::Kingside | Castling::Both)
    }
    /// Can this player castle queenside?
    #[must_use]
    pub fn queenside(self) -> bool {
        matches!(self, Castling::Queenside | Castling::Both)
    }
    /// Can this player castle both sides?
    #[must_use]
    pub fn both(self) -> bool {
        matches!(self, Castling::Both)
    }
    /// Can this player castle neither side?
    #[must_use]
    pub fn neither(self) -> bool {
        matches!(self, Castling::Neither)
    }
    /// Get the "castling spec" in FEN format for this enum. Lowercase.
    #[cfg(feature = "alloc")]
    #[must_use]
    pub fn into_fen_castle_spec(self) -> String {
        match self {
            Self::Neither => String::new(),
            Self::Kingside => String::from("k"),
            Self::Queenside => String::from("q"),
            Self::Both => String::from("kq"),
        }
    }
}

impl Add for Castling {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (_, Castling::Neither)
            | (Castling::Kingside, Castling::Kingside)
            | (Castling::Queenside, Castling::Queenside) => self,

            (Castling::Neither, _) => rhs,

            (Castling::Kingside, Castling::Queenside)
            | (Castling::Queenside, Castling::Kingside)
            | (Castling::Both, _)
            | (_, Castling::Both) => Castling::Both,
        }
    }
}

impl AddAssign for Castling {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

/// A game.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Arbitrary))]
#[cfg_attr(test, proptest(no_params))]
#[cfg_attr(not(feature = "alloc"), derive(Debug))]
pub struct Game {
    /// The current board.
    pub board: Board,
    /// The current player's turn.
    pub turn: Color,
    /// The castling status for black.
    pub black_castling: Castling,
    /// The castling status for white.
    pub white_castling: Castling,
    /// The square over which a pawn has just passed while moving two squares if there is one.
    #[cfg_attr(test, proptest(strategy = "super::non_empty_position_with_option()"))]
    pub last_en_passant: Option<Position>,
    /// The number of half-moves since the last capture or pawn advance, used for the fifty-move rule.
    pub halfmove_clock: u16,
    /// The number of full moves. Starts at one and is incremented after black's turn.
    pub move_number: u16,
}

#[cfg(feature = "alloc")]
impl Debug for Game {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(&self.into_fen())
    }
}

impl Ord for Game {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.move_number.cmp(&other.move_number)
    }
}

impl PartialOrd for Game {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Game {
    /// Get a `Game` from a FEN string.
    ///
    /// # Errors
    /// If there was an error parsing the FEN string, then it is returned.
    #[expect(clippy::missing_panics_doc, reason = "testedly impossible")]
    #[expect(clippy::too_many_lines, reason = "idgaf")]
    pub fn from_fen_u8_slice(s: impl AsRef<[u8]>) -> Result<Self, anyhow::Error> {
        let s = bstr::BStr::new(s.as_ref());
        let mut sections_iter = s.split(|v| *v == b' ');

        let mut get_next_section = || {
            sections_iter
                .next()
                .ok_or(anyhow!("less then five sections in FEN string"))
                .map(bstr::BStr::new)
        };

        let sections = [
            get_next_section()?,
            get_next_section()?,
            get_next_section()?,
            get_next_section()?,
            get_next_section()?,
        ];
        let sixth_section = sections_iter.next();

        let en_passant_square = if sixth_section.is_some() && sections[3] != b"-" {
            ensure!(
                sections[3].len() == 2,
                "en passant field should either be '-' or a valid position"
            );
            Some(
                Position::try_from([
                    char::from_u32(u32::from(sections[3][0])).unwrap(),
                    char::from_u32(u32::from(sections[3][1])).unwrap(),
                ])
                .context("en passant field should either be '-' or a valid position")?,
            )
        } else {
            None
        };

        ensure!(
            sections[0].len() >= 15,
            "board in FEN has to be at least 15 characters (8/8/8/8/8/8/8/8 is minimal)"
        );

        ensure!(
            bytecount::naive_count_32(sections[0], b'/') == 7,
            "board in FEN must have exactly seven slashes"
        );

        let mut board: SmallVec<[Option<(Piece, Color)>; BOARD_WIDTH * BOARD_HEIGHT]> =
            SmallVec::new();

        for row in sections[0].split(|v| *v == b'/') {
            let old_len = board.len();
            for ch in row {
                match ch {
                    b'0' => bail!("cannot add zero empty spaces to board"),
                    b'1' => board.push(None),
                    b'2' => {
                        for _ in 1..=2 {
                            board.push(None);
                        }
                    }
                    b'3' => {
                        for _ in 1..=3 {
                            board.push(None);
                        }
                    }
                    b'4' => {
                        for _ in 1..=4 {
                            board.push(None);
                        }
                    }
                    b'5' => {
                        for _ in 1..=5 {
                            board.push(None);
                        }
                    }
                    b'6' => {
                        for _ in 1..=6 {
                            board.push(None);
                        }
                    }
                    b'7' => {
                        for _ in 1..=7 {
                            board.push(None);
                        }
                    }
                    b'8' => {
                        for _ in 1..=8 {
                            board.push(None);
                        }
                    }
                    b'9' => bail!("cannot add nine empty spaces to board"),
                    b'p' => board.push(Some((Piece::Pawn, Color::Black))),
                    b'P' => board.push(Some((Piece::Pawn, Color::White))),
                    b'n' => board.push(Some((Piece::Knight, Color::Black))),
                    b'N' => board.push(Some((Piece::Knight, Color::White))),
                    b'b' => board.push(Some((Piece::Bishop, Color::Black))),
                    b'B' => board.push(Some((Piece::Bishop, Color::White))),
                    b'r' => board.push(Some((Piece::Rook, Color::Black))),
                    b'R' => board.push(Some((Piece::Rook, Color::White))),
                    b'q' => board.push(Some((Piece::Queen, Color::Black))),
                    b'Q' => board.push(Some((Piece::Queen, Color::White))),
                    b'k' => board.push(Some((Piece::King, Color::Black))),
                    b'K' => board.push(Some((Piece::King, Color::White))),
                    _ => bail!("unknown character in FEN board"),
                }
            }
            ensure!(
                board.len() - old_len <= 8,
                "attempted to add more than eight squares to row"
            );
            ensure!(
                board.len().is_multiple_of(8),
                "attempted to add less than eight squares to row"
            );
        }
        ensure!(
            board.len() == board.capacity(),
            "FEN is too short; expected exactly 64 cells"
        );

        let board = Board(board.into_inner().unwrap());

        let turn = match sections[1] as &[u8] {
            b"w" => Color::White,
            b"b" => Color::Black,
            b"W" | b"B" => bail!("color in FEN must be lowercase"),
            _ => bail!("unknown FEN color string, should be either 'w' or 'b'"),
        };

        let mut white_castling = Castling::Neither;
        let mut black_castling = Castling::Neither;

        for b in sections[2].bytes() {
            match b {
                b'-' => break,
                b'K' => white_castling += Castling::Kingside,
                b'Q' => white_castling += Castling::Queenside,
                b'k' => black_castling += Castling::Kingside,
                b'q' => black_castling += Castling::Queenside,
                _ => bail!("unknown character in allowed castling positions"),
            }
        }

        let halfmove_clock =
            from_decimal_u16(sections[if sixth_section.is_some() { 4 } else { 3 }])
                .context("invalid halfmove clock value")?;

        let fullmove_num = from_decimal_u16(if let Some(sixth_section) = sixth_section {
            sixth_section
        } else {
            sections[4]
        })
        .context("invalid fullmove number value")?;

        Ok(Self {
            board,
            turn,
            black_castling,
            white_castling,
            last_en_passant: en_passant_square,
            halfmove_clock,
            move_number: fullmove_num,
        })
    }
    /// Get a `Game` from a FEN string.
    ///
    /// # Errors
    /// If there was an error parsing the FEN string, then it is returned.
    #[cfg(feature = "alloc")]
    pub fn parse_fen(s: impl AsRef<str>) -> Result<Self, anyhow::Error> {
        Self::from_fen_u8_slice(s.as_ref().bytes().collect::<Vec<u8>>().as_slice())
    }
    /// Get the FEN string for this `Game`.
    #[must_use]
    #[cfg(feature = "alloc")]
    pub fn into_fen(self) -> String {
        let mut out = self.board.into_fen_board();

        out.push(' ');

        match self.turn {
            Color::Black => out.push('b'),
            Color::White => out.push('w'),
        }

        out.push(' ');

        let castling_spec = self.white_castling.into_fen_castle_spec().to_uppercase()
            + &self.black_castling.into_fen_castle_spec();

        if castling_spec.is_empty() {
            out.push('-');
        } else {
            out.push_str(&castling_spec);
        }

        out.push(' ');

        match self.last_en_passant {
            None => out.push('-'),
            Some(pos) => out.push_str(&pos.to_string()),
        }

        out.push(' ');

        out.push_str(&format!("{}", self.halfmove_clock));

        out.push(' ');

        out.push_str(&format!("{}", self.move_number));

        out
    }
}
