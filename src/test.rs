use super::*;
use alloc::{
    format,
    string::{String, ToString},
};
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_position_parsing_unicode(s in "\\PC*") {
        let _ = <&str as TryInto<Position>>::try_into(&s);
    }
    #[test]
    fn parse_all_valid_positions(s in "[a-h?][1-8?]") {
        <&str as TryInto<Position>>::try_into(&s).unwrap();
    }
    #[test]
    fn parse_all_positions_correctly(rank in 0u8..=7u8, file in 0u8..=7u8) {
        assert_eq!(<&str as TryInto<Position>>::try_into(
            &format!("{}{}",
                char::from_u32(u32::from(b'a') + u32::from(file)
            ).unwrap(), rank + 1)
        ).unwrap(), Position::try_from((file, rank)).unwrap());
    }
    #[test]
    fn test_algebraic_parsing_unicode(s in "\\PC*") {
        let _ = Move::parse_alg(&s, None);
        let _ = Move::parse_alg(&s, Some(Color::Black));
        let _ = Move::parse_alg(&s, Some(Color::White));
    }
    #[test]
    fn parse_all_valid_algebraic1(s in "[♔♚♕♛♖♜♗♝♘♞♙♟KQRBN]?([a-h][1-8])?[x×:]?[a-h][1-8]([+†]|\\+\\+|[#‡≠Xx])?") {
        let _ = Move::parse_alg(&s, None).unwrap();
        let _ = Move::parse_alg(&s, Some(Color::Black)).unwrap();
        let _ = Move::parse_alg(&s, Some(Color::White)).unwrap();
    }
    #[test]
    fn parse_all_valid_algebraic2(s in "[♔♚♕♛♖♜♗♝♘♞♙♟KQRBN][a-h]?[1-8]?[x×:]?[a-h][1-8]([+†]|\\+\\+|[#‡≠Xx])?") {
        let _ = Move::parse_alg(&s, None).unwrap();
        let _ = Move::parse_alg(&s, Some(Color::Black)).unwrap();
        let _ = Move::parse_alg(&s, Some(Color::White)).unwrap();
    }
    #[test]
    fn parse_all_algebraic_correctly1(
        piece in "[♔♚♕♛♖♜♗♝♘♞♙♟KQRBN]?",
        rank in 0u8..=7u8,
        file in 0u8..=7u8,
        from_rank in 0u8..=8u8,
        from_file in 0u8..=8u8,
        check: bool,
        checkmate: bool,
        capturing: bool,
    ) {
        const COLORS: [Option<Color>; 3] = [None, Some(Color::Black), Some(Color::White)];
        if check && checkmate {
            return Ok(());
        }
        let pos = Position::try_from((file, rank)).unwrap();
        let (piece, piece_color) = if piece.is_empty() {
            (Piece::Pawn, None)
        } else {
            Piece::from_piece_char_strict(piece.chars().next().unwrap()).unwrap()
        };

        for mut color in COLORS {
            if let Some(piece_color) = piece_color {
                color = Some(piece_color);
            }

            let chess_move = format!("{piece}{}{}{pos}{}", if from_rank < 8 && from_file < 8 {
                Position::try_from((from_file, from_rank)).unwrap().to_string()
            } else if from_rank < 8 {
                Position::try_from((None, Some(from_rank))).unwrap().to_string().replace('?', "")
            } else if from_file < 8 {
                Position::try_from((Some(from_file), None)).unwrap().to_string().replace('?', "")
            } else {
                String::new()
            }, if capturing {
                "x"
            } else {
                ""
            }, if check {
                "+"
            } else if checkmate {
                "#"
            } else {
                ""
            });

            assert_eq!(Move::parse_alg(&chess_move, color).unwrap(), Move {
                from: if from_rank < 8 && from_file < 8 {
                    Some(Position::try_from((from_file, from_rank)).unwrap())
                } else if from_rank < 8 {
                    Some(Position::try_from((None, Some(from_rank))).unwrap())
                } else if from_file < 8 {
                    Some(Position::try_from((Some(from_file), None)).unwrap())
                } else {
                    None
                },
                to: pos,
                piece,
                color,
                capturing: Some(capturing),
                castling: Some(false),
                promotion: None,
                into_check: if check {
                    Some(true)
                } else {
                    None
                },
                into_checkmate: if checkmate {
                    Some(true)
                } else {
                    None
                },
                move_num: None,
            });
        }
    }
}

#[test]
fn castling_parse_algebraic() {
    const KINGSIDE_STRS: [&str; 2] = ["0-0", "O-O"];
    const QUEENSIDE_STRS: [&str; 2] = ["0-0-0", "O-O-O"];
    const COMBINED_STRS: [&str; 4] = ["0-0", "O-O", "0-0-0", "O-O-O"];

    for s in COMBINED_STRS {
        assert!(Move::parse_alg(s, None).is_err());
        Move::parse_alg(s, Some(Color::Black)).unwrap();
        Move::parse_alg(s, Some(Color::White)).unwrap();
    }

    for s in KINGSIDE_STRS {
        assert_eq!(
            Move::parse_alg(s, Some(Color::White)).unwrap(),
            Move {
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
            }
        );
        assert_eq!(
            Move::parse_alg(s, Some(Color::Black)).unwrap(),
            Move {
                from: Some(position!("e8")),
                to: position!("g8"),
                piece: Piece::King,
                color: Some(Color::Black),
                capturing: Some(false),
                castling: Some(true),
                promotion: None,
                into_check: None,
                into_checkmate: None,
                move_num: None
            }
        );
    }

    for s in QUEENSIDE_STRS {
        assert_eq!(
            Move::parse_alg(s, Some(Color::White)).unwrap(),
            Move {
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
            }
        );
        assert_eq!(
            Move::parse_alg(s, Some(Color::Black)).unwrap(),
            Move {
                from: Some(position!("e8")),
                to: position!("c8"),
                piece: Piece::King,
                color: Some(Color::Black),
                capturing: Some(false),
                castling: Some(true),
                promotion: None,
                into_check: None,
                into_checkmate: None,
                move_num: None
            }
        );
    }
}