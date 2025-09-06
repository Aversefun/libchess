//! Rust chess library
#![warn(
    missing_docs,
    clippy::missing_docs_in_private_items,
    clippy::pedantic,
    clippy::all,
    clippy::ignore_without_reason
)]
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use core::{
    error::Error,
    fmt::{Debug, Display},
    hint::unreachable_unchecked,
};

use anyhow::{anyhow, bail, ensure};

/// The color of a piece.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[expect(missing_docs, reason = "people know what colors are")]
pub enum Color {
    White,
    Black,
}

impl Color {
    /// Is this piece white?
    #[must_use]
    pub fn white(self) -> bool {
        matches!(self, Self::White)
    }
    /// Is this piece black?
    #[must_use]
    pub fn black(self) -> bool {
        matches!(self, Self::Black)
    }
}

/// A piece.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Piece {
    /// King - value [`u8::MAX`] (255).
    King,
    /// Queen - value 9.
    Queen,
    /// Rook - value 5.
    Rook,
    /// Bishop - value 3.
    Bishop,
    /// Knight - value 3.
    Knight,
    /// Pawn - value 1.
    Pawn,
}

impl Piece {
    /// Whether the character matches the standard uppercase english acronyms 'KQRBN' or is within
    /// "♔♕♖♗♘♙♚♛♜♝♞♟".
    #[must_use]
    pub fn is_valid_piece_char_strict(ch: char) -> bool {
        ['K', 'Q', 'R', 'B', 'N'].contains(&ch) || (0x2654..0x265F).contains(&(ch as u32))
    }
    /// Whether the character matches the standard uppercase or lowercase english acronyms 'KQRBN'
    /// or is within "♔♕♖♗♘♙♚♛♜♝♞♟".
    #[must_use]
    pub fn is_valid_piece_char(ch: char) -> bool {
        Self::is_valid_piece_char_strict(ch.to_ascii_uppercase())
    }
    /// Get the piece and possibly color from the provided character. Matches the characters from
    /// [`is_valid_piece_char_strict`](Self::is_valid_piece_char_strict).
    #[must_use]
    pub fn from_piece_char_strict(ch: char) -> Option<(Self, Option<Color>)> {
        match ch {
            'K' => Some((Self::King, None)),
            'Q' => Some((Self::Queen, None)),
            'R' => Some((Self::Rook, None)),
            'B' => Some((Self::Bishop, None)),
            'N' => Some((Self::Knight, None)),
            '♔' => Some((Self::King, Some(Color::White))),
            '♕' => Some((Self::Queen, Some(Color::White))),
            '♖' => Some((Self::Rook, Some(Color::White))),
            '♗' => Some((Self::Bishop, Some(Color::White))),
            '♘' => Some((Self::Knight, Some(Color::White))),
            '♙' => Some((Self::Pawn, Some(Color::White))),
            '♚' => Some((Self::King, Some(Color::Black))),
            '♛' => Some((Self::Queen, Some(Color::Black))),
            '♜' => Some((Self::Rook, Some(Color::Black))),
            '♝' => Some((Self::Bishop, Some(Color::Black))),
            '♞' => Some((Self::Knight, Some(Color::Black))),
            '♟' => Some((Self::Pawn, Some(Color::Black))),
            _ => None,
        }
    }
    /// Get the piece and possibly color from the provided character. Matches the characters from
    /// [`is_valid_piece_char`](Self::is_valid_piece_char).
    #[must_use]
    pub fn from_piece_char(ch: char) -> Option<(Self, Option<Color>)> {
        Self::from_piece_char_strict(ch.to_ascii_uppercase())
    }
}

impl From<Piece> for u8 {
    fn from(val: Piece) -> Self {
        match val {
            Piece::King => u8::MAX,
            Piece::Queen => 9,
            Piece::Rook => 5,
            Piece::Bishop | Piece::Knight => 3,
            Piece::Pawn => 1,
        }
    }
}

impl From<&Piece> for u8 {
    fn from(value: &Piece) -> Self {
        (*value).into()
    }
}

impl Ord for Piece {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        <&Piece as Into<u8>>::into(self).cmp(&other.into())
    }
}

impl PartialOrd for Piece {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// A position on the board.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Position {
    /// The packed position. 0bghrrrfff where r is rank, f is file, g is whether it has rank,
    /// and h is whether it has file.
    packed_pos: u8,
}

impl Position {
    /// Does this position have rank?
    #[must_use]
    pub fn has_rank(self) -> bool {
        self.packed_pos & 0b100_0000 == 0b100_0000
    }
    /// Does this position have file?
    #[must_use]
    pub fn has_file(self) -> bool {
        self.packed_pos & 0b1000_0000 == 0b1000_0000
    }
    /// Get the rank of this position. One-based.
    #[must_use]
    pub fn rank(self) -> Option<u8> {
        <Position as core::convert::Into<(Option<u8>, Option<u8>)>>::into(self).1
    }
    /// Get the file of this position. One-based.
    #[must_use]
    pub fn file(self) -> Option<u8> {
        <Position as core::convert::Into<(Option<u8>, Option<u8>)>>::into(self).0
    }
    /// Get the index of this position. Zero-based, perfect for arrays.
    #[must_use]
    pub fn index(self) -> Option<usize> {
        Some(((self.file()? - 1) + ((self.rank()? - 1) * 8)) as usize)
    }
}

/// An error with the size of a position.
pub enum PositionError {
    /// Too large rank.
    TooLargeRank,
    /// Too large file.
    TooLargeFile,
    /// Too large rank and file.
    TooLargeRankAndFile,
}

impl Display for PositionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Self::TooLargeFile => f.write_str("file should be between 0 and 7"),
            Self::TooLargeRank => f.write_str("rank should be between 0 and 7"),
            Self::TooLargeRankAndFile => f.write_str("rank and file should be between 0 and 7"),
        }
    }
}

impl Debug for PositionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_fmt(format_args!("{self}"))
    }
}

impl Error for PositionError {}

impl TryFrom<(Option<u8>, Option<u8>)> for Position {
    type Error = PositionError;
    fn try_from(value: (Option<u8>, Option<u8>)) -> Result<Self, Self::Error> {
        if value.0.unwrap_or(0) >= 8 && value.1.unwrap_or(0) >= 8 {
            return Err(PositionError::TooLargeRankAndFile);
        } else if value.0.unwrap_or(0) >= 8 {
            return Err(PositionError::TooLargeFile);
        } else if value.1.unwrap_or(0) >= 8 {
            return Err(PositionError::TooLargeRank);
        }

        Ok(Self {
            packed_pos: (value.1.unwrap_or(0) & 0b111) | ((value.0.unwrap_or(0) & 0b111) << 3) | if value.1.is_some() {
                0b1000_0000
            } else {
                0
            } | if value.0.is_some() {
                0b0100_0000
            } else {
                0
            },
        })
    }
}

impl TryFrom<(u8, u8)> for Position {
    type Error = PositionError;
    fn try_from(value: (u8, u8)) -> Result<Self, Self::Error> {
        if value.0 >= 8 && value.1 >= 8 {
            return Err(PositionError::TooLargeRankAndFile);
        } else if value.0 >= 8 {
            return Err(PositionError::TooLargeFile);
        } else if value.1 >= 8 {
            return Err(PositionError::TooLargeRank);
        }

        Ok(Self {
            packed_pos: (value.1 & 0b111) | ((value.0 & 0b111) << 3) | 0b1100_0000,
        })
    }
}

impl Ord for Position {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        let pos1: (Option<u8>, Option<u8>) = self.into();
        let pos2: (Option<u8>, Option<u8>) = other.into();

        pos1.cmp(&pos2)
    }
}

impl PartialOrd for Position {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl From<&Position> for (Option<u8>, Option<u8>) {
    fn from(value: &Position) -> Self {
        (*value).into()
    }
}

impl From<Position> for (Option<u8>, Option<u8>) {
    fn from(value: Position) -> Self {
        let file = (value.packed_pos & 0b111) + 1;
        let rank = ((value.packed_pos & 0b111_000) >> 3) + 1;
        (if value.has_file() {
            Some(file)
        } else {
            None
        }, if value.has_rank() {
            Some(rank)
        } else {
            None
        })
    }
}

impl From<Position> for [char; 2] {
    fn from(value: Position) -> Self {
        let (file, rank) = value.into();
        let file_char = match file {
            Some(1) => 'a',
            Some(2) => 'b',
            Some(3) => 'c',
            Some(4) => 'd',
            Some(5) => 'e',
            Some(6) => 'f',
            Some(7) => 'g',
            Some(8) => 'h',
            None => '?',
            // SAFETY: Physically impossible for three bits to store more then 7. 1 is added.
            _ => unsafe { unreachable_unchecked() },
        };
        let rank_char = match rank {
            Some(1) => '1',
            Some(2) => '2',
            Some(3) => '3',
            Some(4) => '4',
            Some(5) => '5',
            Some(6) => '6',
            Some(7) => '7',
            Some(8) => '8',
            None => '?',
            // SAFETY: Physically impossible for three bits to store more then 7. 1 is added.
            _ => unsafe { unreachable_unchecked() },
        };
        [file_char, rank_char]
    }
}

impl TryFrom<[char; 2]> for Position {
    type Error = anyhow::Error;
    fn try_from(value: [char; 2]) -> Result<Self, Self::Error> {
        let file: u8 = match value[0] {
            'a' => 1,
            'b' => 2,
            'c' => 3,
            'd' => 4,
            'e' => 5,
            'f' => 6,
            'g' => 7,
            'h' => 8,
            _ => bail!("bad file"),
        };

        let rank: u8 = match value[1] {
            '1' => 1,
            '2' => 2,
            '3' => 3,
            '4' => 4,
            '5' => 5,
            '6' => 6,
            '7' => 7,
            '8' => 8,
            _ => bail!("bad rank"),
        };
        Ok(Self::try_from((file, rank)).unwrap())
    }
}

impl TryFrom<&str> for Position {
    type Error = anyhow::Error;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        ensure!(value.len() == 2, "&str should be exactly length 2");

        let mut iter = value.chars();
        let arr = [iter.next().unwrap(), iter.next().unwrap()];
        <[char; 2] as TryInto<Position>>::try_into(arr)
    }
}

/// Convinence macro for creating a [`Position`] from something like "a4".
#[macro_export]
macro_rules! position {
    ($pos:literal) => {
        <&str as TryInto<Position>>::try_into($pos).unwrap()
    };
}

/// A move.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Move {
    /// If known, the position that the piece if moving from.
    pub from: Option<Position>,
    /// The position the piece is moving to.
    pub to: Position,
    /// The type of piece that is moving.
    pub piece: Piece,
    /// The color of the piece, if known.
    pub color: Option<Color>,
    /// If known, whether the piece is capturing.
    pub capturing: Option<bool>,
    /// If known, whether the piece is castling. If true, then this specifies the king's
    /// movement.
    pub castling: Option<bool>,
    /// If this is a pawn promoting, the piece it is promoting to.
    pub promotion: Option<Piece>,
    /// If known, whether this move puts the opponent into check.
    pub into_check: Option<bool>,
    /// If known, whether this move puts the opponent into checkmate.
    pub into_checkmate: Option<bool>,
    /// If known, the move number. One-based.
    pub move_num: Option<usize>,
}

impl Move {
    /// Parse an algebraic notation slice of characters into a [`Move`].
    /// 
    /// # Errors
    /// If there was an error parsing the algebraic notation, it's returned.
    #[expect(clippy::missing_panics_doc, reason = "ideally false")]
    #[expect(clippy::too_many_lines, reason = "idgaf")]
    pub fn parse_alg_char_slice(s: impl AsRef<[char]>, user_color: Option<Color>) -> Result<Self, anyhow::Error> {
        fn character_is_capturing(ch: char) -> bool {
            ['x', '×', ':'].contains(&ch)
        }

        let mut s = s.as_ref();
        ensure!(
            s.len() >= 2,
            "one move in algebraic notation must be at least two characters"
        );

        let check = if ['+', '†'].contains(&s[s.len() - 1]) {
            s = &s[..s.len() - 1]; // remove last character
            Some(true)
        } else if s.ends_with(&['c', 'h']) {
            s = &s[..s.len() - 2]; // remove last two characters
            Some(true)
        } else if s.ends_with(&['d', 'i', 's', ' ', 'c', 'h'])
            || s.ends_with(&['d', 'b', 'l', ' ', 'c', 'h'])
        {
            s = &s[..s.len() - 6]; // remove last six characters
            Some(true)
        } else if s.ends_with(&['+', '+']) {
            // could be check or checkmate
            s = &s[..s.len() - 2]; // remove last two characters
            None
        } else {
            None
        };

        ensure!(s.len() >= 2, "bad length");

        let checkmate = if ['#', '‡', '≠', 'X', 'x'].contains(&s[s.len() - 1]) {
            s = &s[..s.len() - 1]; // remove last character
            Some(true)
        } else if s.ends_with(&['c', 'h']) {
            s = &s[..s.len() - 2]; // remove last two characters
            Some(true)
        } else if s.ends_with(&['+', '+']) {
            // could be check or checkmate
            s = &s[..s.len() - 2]; // remove last two characters
            None
        } else {
            None
        };
        
        ensure!(s.len() >= 2, "bad length");

        #[expect(clippy::nonminimal_bool, reason = "it only makes it more complex")]
        let castling = (s[0] == '0' && s[1] == '-') || (s[0] == 'O' && s[1] == '-');

        let (piece, color) = if castling {
            (Piece::King, None)
        } else if Piece::is_valid_piece_char_strict(s[0]) {
            // assume that it is the piece. strict since B is both bishop and file B.
            let ch = s[0];
            s = &s[1..];
            Piece::from_piece_char_strict(ch).unwrap()
        } else {
            // could be lowercase piece, could be pawn
            if s.len() == 2 {
                // definitely pawn
                (Piece::Pawn, None)
            } else {
                let ch = s[0];
                s = &s[1..];
                Piece::from_piece_char(ch).ok_or(anyhow!(
                    "bad piece spec; currently only english piece abbreviations are supported"
                ))?
            }
        };

        ensure!(s.len() >= 2, "bad length");

        #[expect(clippy::cast_possible_truncation, reason = "i couldn't give a shit")]
        let from = if s.len() == 3 && !character_is_capturing(s[0]) && !castling {
            let ch = s[0];
            s = &s[1..];
            if ch.is_ascii_digit() {
                // A rank
                Some(Position::try_from((None, Some(ch as u32 as u8 - b'0')))?)
            } else if ch.is_ascii_alphabetic() {
                // A file
                Some(Position::try_from((Some(ch.to_ascii_lowercase() as u32 as u8 - b'a'), None))?)
            } else {
                bail!("unknown character; expected from position")
            }
        } else if (4..=5).contains(&s.len()) && !castling {
            let ch = [s[0], s[1]];
            s = &s[2..];

            ensure!(ch[0].is_ascii_alphabetic(), "bad from file (not ascii alphabetic)");
            ensure!(ch[0].is_ascii_digit(), "bad from rank (not ascii digit)");

            Some(Position::try_from((Some(ch[0].to_ascii_lowercase() as u32 as u8 - b'a'), Some(ch[1] as u32 as u8 - b'0')))?)
        } else {
            None
        };
        
        let capturing = if castling {
            false
        } else if character_is_capturing(s[0]) {
            s = &s[1..];
            true
        } else {
            false
        };

        ensure!(s.len() >= 2, "bad length");

        let (from, to, could_promote) = if castling {
            let queenside = s.len() >= 5;
            if let Some(user_color) = user_color {
                match user_color {
                    Color::White => {
                        if queenside {
                            (Some(position!("e1")), position!("c1"), false)
                        } else {
                            (Some(position!("e1")), position!("g1"), false)
                        }
                    }
                    Color::Black => {
                        if queenside {
                            (Some(position!("e8")), position!("c8"), false)
                        } else {
                            (Some(position!("e8")), position!("g8"), false)
                        }
                    }
                }
            } else {
                bail!("attempted to get move for castle without providing color")
            }
        } else {
            (from, Position::try_from([s[0], s[1]])?, s.len() > 2)
        };

        let promotion = if could_promote {
            match s.len() {
                // SAFETY: can only get to this branch if s.len() is at least 3
                0..=2 => unsafe {unreachable_unchecked()},
                3 => {
                    Some(Piece::from_piece_char(s[2]).ok_or(anyhow!("invalid promotion piece"))?.0)
                }
                4.. => {
                    // probably fourth symbol - any extra characters are ignored
                    Some(Piece::from_piece_char(s[3]).ok_or(anyhow!("invalid promotion piece"))?.0)
                }
            }
        } else {
            None
        };

        Ok(Move {
            from,
            to,
            piece,
            color: color.or(user_color),
            capturing: Some(capturing),
            castling: Some(castling),
            promotion,
            into_check: check,
            into_checkmate: checkmate,
            move_num: None,
        })
    }
    /// Parse an algebraic notation slice of characters into a [`Move`].
    /// 
    /// # Errors
    /// If there was an error parsing the algebraic notation, it's returned.
    #[cfg(feature = "alloc")]
    pub fn parse_alg(s: impl AsRef<str>, color: Option<Color>) -> Result<Self, anyhow::Error> {
        Self::parse_alg_char_slice(s.as_ref().chars().collect::<Vec<char>>().as_slice(), color)
    }
}

impl PartialOrd for Move {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.move_num
            .and_then(|v1| other.move_num.map(|v2| v1.cmp(&v2)))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_alg_char_slice() {
        assert_eq!(Move::parse_alg("Nf3", Some(Color::Black)).unwrap(), Move {
            from: None,
            to: position!("f3"),
            piece: Piece::Knight,
            color: Some(Color::Black),
            capturing: Some(false),
            castling: Some(false),
            promotion: None,
            into_check: None,
            into_checkmate: None,
            move_num: None
        });
        assert_eq!(Move::parse_alg("Rc2#", Some(Color::White)).unwrap(), Move {
            from: None,
            to: position!("c2"),
            piece: Piece::Rook,
            color: Some(Color::White),
            capturing: Some(false),
            castling: Some(false),
            promotion: None,
            into_check: None,
            into_checkmate: Some(true),
            move_num: None
        });
        assert_eq!(Move::parse_alg("Nxe1", None).unwrap(), Move {
            from: None,
            to: position!("e1"),
            piece: Piece::Knight,
            color: None,
            capturing: Some(true),
            castling: Some(false),
            promotion: None,
            into_check: None,
            into_checkmate: None,
            move_num: None
        });
        assert_eq!(Move::parse_alg("O-O", Some(Color::White)).unwrap(), Move {
            from: Some(position!("e1")),
            to: position!("g1"),
            piece: Piece::King,
            color: Some(Color::White),
            capturing: Some(false),
            castling: Some(true),
            promotion: None,
            into_check: None,
            into_checkmate: None,
            move_num: None
        });

        assert_eq!(Move::parse_alg("O-O-O", Some(Color::White)).unwrap(), Move {
            from: Some(position!("e1")),
            to: position!("c1"),
            piece: Piece::King,
            color: Some(Color::White),
            capturing: Some(false),
            castling: Some(true),
            promotion: None,
            into_check: None,
            into_checkmate: None,
            move_num: None
        });

        assert_eq!(Move::parse_alg("0-0-0", Some(Color::White)).unwrap(), Move {
            from: Some(position!("e1")),
            to: position!("c1"),
            piece: Piece::King,
            color: Some(Color::White),
            capturing: Some(false),
            castling: Some(true),
            promotion: None,
            into_check: None,
            into_checkmate: None,
            move_num: None
        });

        assert_eq!(Move::parse_alg("♕a6", Some(Color::Black)).unwrap(), Move {
            from: None,
            to: position!("a6"),
            piece: Piece::Queen,
            color: Some(Color::White),
            capturing: Some(false),
            castling: Some(false),
            promotion: None,
            into_check: None,
            into_checkmate: None,
            move_num: None
        });
    }
}
