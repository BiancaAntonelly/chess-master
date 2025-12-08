package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessMatch;
import chess.ChessPiece;
import chess.Color;

public class King extends ChessPiece {

    //@ spec_public
    private final /*@ non_null @*/ ChessMatch match;

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   requires match != null;
      @   ensures this.getMoveCount() == 0;
      @   ensures getBoard() == board;
      @   ensures this.match == match;
      @*/
    public King(/*@ non_null @*/ Board board,
            /*@ non_null @*/ Color color,
            /*@ non_null @*/ ChessMatch match) {
        super(board, color);
        this.match = match;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("K");
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "K";
    }

    private boolean canMove(/*@ non_null @*/ Position position) {
        ChessPiece p = (ChessPiece) getBoard().piece(position);
        return p == null || p.getColor() != getColor();
    }

    private boolean testRookCastling(/*@ non_null @*/ Position position) {
        ChessPiece p = (ChessPiece) getBoard().piece(position);
        return p != null && p instanceof Rook &&
                p.getColor() == getColor() &&
                p.getMoveCount() == 0;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @*/
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

        boolean[][] mat = new boolean[board.getRows()][board.getCols()];
        Position p = new Position(0, 0);

        // acima
        p.setValues(currentPos.getRow() - 1, currentPos.getCol());
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // abaixo
        p.setValues(currentPos.getRow() + 1, currentPos.getCol());
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // esquerda
        p.setValues(currentPos.getRow(), currentPos.getCol() - 1);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // direita
        p.setValues(currentPos.getRow(), currentPos.getCol() + 1);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // diagonal noroeste
        p.setValues(currentPos.getRow() - 1, currentPos.getCol() - 1);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // diagonal nordeste
        p.setValues(currentPos.getRow() - 1, currentPos.getCol() + 1);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // diagonal sudoeste
        p.setValues(currentPos.getRow() + 1, currentPos.getCol() - 1);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // diagonal sudeste
        p.setValues(currentPos.getRow() + 1, currentPos.getCol() + 1);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // Roque
        if (getMoveCount() == 0 && !match.getCheck()) {
            // Roque pequeno (rei para a direita)
            Position posT1 = new Position(currentPos.getRow(), currentPos.getCol() + 3);
            if (testRookCastling(posT1)) {
                Position p1 = new Position(currentPos.getRow(), currentPos.getCol() + 1);
                Position p2 = new Position(currentPos.getRow(), currentPos.getCol() + 2);
                if (board.piece(p1) == null && board.piece(p2) == null) {
                    int r = currentPos.getRow();
                    int c = currentPos.getCol() + 2;
                    if (r >= 0 && r < mat.length) {
                        if (c >= 0 && c < mat[r].length) {
                            mat[r][c] = true;
                        }
                    }
                }
            }

            // Roque grande (rei para a esquerda)
            Position posT2 = new Position(currentPos.getRow(), currentPos.getCol() - 4);
            if (testRookCastling(posT2)) {
                Position p1 = new Position(currentPos.getRow(), currentPos.getCol() - 1);
                Position p2 = new Position(currentPos.getRow(), currentPos.getCol() - 2);
                Position p3 = new Position(currentPos.getRow(), currentPos.getCol() - 3);
                if (board.piece(p1) == null &&
                        board.piece(p2) == null &&
                        board.piece(p3) == null) {
                    int r = currentPos.getRow();
                    int c = currentPos.getCol() - 2;
                    if (r >= 0 && r < mat.length) {
                        if (c >= 0 && c < mat[r].length) {
                            mat[r][c] = true;
                        }
                    }
                }
            }
        }

        return mat;
    }
}
