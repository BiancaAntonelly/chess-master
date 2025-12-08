package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessMatch;
import chess.ChessPiece;
import chess.Color;

public class Pawn extends ChessPiece {

    //@ public invariant match != null;

    //@ spec_public
    private final /*@ non_null @*/ ChessMatch match;

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   requires match != null;
      @   ensures getMoveCount() == 0;
      @   ensures getBoard() == board;
      @   ensures this.match == match;
      @*/
    public Pawn(/*@ non_null @*/ Board board,
            /*@ non_null @*/ Color color,
            /*@ non_null @*/ ChessMatch match) {
        super(board, color);
        this.match = match;
    }

    @Override
    public boolean[][] possibleMoves() {
        if (position == null || getBoard() == null) {
            return new boolean[8][8];
        }
        
        Position currentPos = position;
        Board board = getBoard();
        if (currentPos == null || board == null) {
            return new boolean[8][8];
        }

        int rows = board.getRows();
        int cols = board.getCols();
        boolean[][] mat = new boolean[rows][cols];
        Position p = new Position(0, 0);

        if (getColor() == Color.WHITE) {
            // Um para frente (brancas sobem - row decresce)
            p.setValues(currentPos.getRow() - 1, currentPos.getCol());
            if (board.positionExists(p) && !board.isPiecePlaced(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < rows) {
                    if (c >= 0 && c < cols) {
                        boolean[] row = mat[r];
                        if (row != null && c < row.length) {
                            row[c] = true;
                        }
                    }
                }

                // Dois para frente (primeiro movimento)
                p.setValues(currentPos.getRow() - 2, currentPos.getCol());
                if (board.positionExists(p) && !board.isPiecePlaced(p) && getMoveCount() == 0) {
                    r = p.getRow();
                    c = p.getCol();
                    if (r >= 0 && r < rows) {
                        if (c >= 0 && c < cols) {
                            boolean[] row = mat[r];
                            if (row != null && c < row.length) {
                                row[c] = true;
                            }
                        }
                    }
                }
            }

            // Captura diagonal esquerda
            p.setValues(currentPos.getRow() - 1, currentPos.getCol() - 1);
            if (board.positionExists(p) && isThereOpponentPiece(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < rows) {
                    if (c >= 0 && c < cols) {
                        boolean[] row = mat[r];
                        if (row != null && c < row.length) {
                            row[c] = true;
                        }
                    }
                }
            }

            // Captura diagonal direita
            p.setValues(currentPos.getRow() - 1, currentPos.getCol() + 1);
            if (board.positionExists(p) && isThereOpponentPiece(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < rows) {
                    if (c >= 0 && c < cols) {
                        boolean[] row = mat[r];
                        if (row != null && c < row.length) {
                            row[c] = true;
                        }
                    }
                }
            }

            // En Passant (brancas)
            if (currentPos.getRow() == 3) {
                Position left = new Position(currentPos.getRow(), currentPos.getCol() - 1);
                if (board.positionExists(left)
                        && isThereOpponentPiece(left)
                        && board.piece(left) == match.getEnPassantVulnerable()) {
                    int r = left.getRow() - 1;
                    int c = left.getCol();
                    if (r >= 0 && r < rows) {
                        if (c >= 0 && c < cols) {
                            boolean[] row = mat[r];
                            if (row != null && c < row.length) {
                                row[c] = true;
                            }
                        }
                    }
                }
                Position right = new Position(currentPos.getRow(), currentPos.getCol() + 1);
                if (board.positionExists(right)
                        && isThereOpponentPiece(right)
                        && board.piece(right) == match.getEnPassantVulnerable()) {
                    int r = right.getRow() - 1;
                    int c = right.getCol();
                    if (r >= 0 && r < rows) {
                        if (c >= 0 && c < cols) {
                            boolean[] row = mat[r];
                            if (row != null && c < row.length) {
                                row[c] = true;
                            }
                        }
                    }
                }
            }
        } else {
            // Um para frente (pretas descem - row aumenta)
            p.setValues(currentPos.getRow() + 1, currentPos.getCol());
            if (board.positionExists(p) && !board.isPiecePlaced(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < rows) {
                    if (c >= 0 && c < cols) {
                        boolean[] row = mat[r];
                        if (row != null && c < row.length) {
                            row[c] = true;
                        }
                    }
                }

                // Dois para frente (primeiro movimento)
                p.setValues(currentPos.getRow() + 2, currentPos.getCol());
                if (board.positionExists(p) && !board.isPiecePlaced(p) && getMoveCount() == 0) {
                    r = p.getRow();
                    c = p.getCol();
                    if (r >= 0 && r < rows) {
                        if (c >= 0 && c < cols) {
                            boolean[] row = mat[r];
                            if (row != null && c < row.length) {
                                row[c] = true;
                            }
                        }
                    }
                }
            }

            // Captura diagonal esquerda (pretas)
            p.setValues(currentPos.getRow() + 1, currentPos.getCol() - 1);
            if (board.positionExists(p) && isThereOpponentPiece(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < rows) {
                    if (c >= 0 && c < cols) {
                        boolean[] row = mat[r];
                        if (row != null && c < row.length) {
                            row[c] = true;
                        }
                    }
                }
            }

            // Captura diagonal direita (pretas)
            p.setValues(currentPos.getRow() + 1, currentPos.getCol() + 1);
            if (board.positionExists(p) && isThereOpponentPiece(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < rows) {
                    if (c >= 0 && c < cols) {
                        boolean[] row = mat[r];
                        if (row != null && c < row.length) {
                            row[c] = true;
                        }
                    }
                }
            }

            // En Passant (pretas)
            if (currentPos.getRow() == 4) {
                Position left = new Position(currentPos.getRow(), currentPos.getCol() - 1);
                if (board.positionExists(left)
                        && isThereOpponentPiece(left)
                        && board.piece(left) == match.getEnPassantVulnerable()) {
                    int r = left.getRow() + 1;
                    int c = left.getCol();
                    if (r >= 0 && r < rows) {
                        if (c >= 0 && c < cols) {
                            boolean[] row = mat[r];
                            if (row != null && c < row.length) {
                                row[c] = true;
                            }
                        }
                    }
                }
                Position right = new Position(currentPos.getRow(), currentPos.getCol() + 1);
                if (board.positionExists(right)
                        && isThereOpponentPiece(right)
                        && board.piece(right) == match.getEnPassantVulnerable()) {
                    int r = right.getRow() + 1;
                    int c = right.getCol();
                    if (r >= 0 && r < rows) {
                        if (c >= 0 && c < cols) {
                            boolean[] row = mat[r];
                            if (row != null && c < row.length) {
                                row[c] = true;
                            }
                        }
                    }
                }
            }
        }

        return mat;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("P");
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "P";
    }
}
