package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessPiece;
import chess.Color;

public class Knight extends ChessPiece {

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getMoveCount() == 0;
      @   ensures getBoard() == board;
      @*/
    public Knight(/*@ non_null @*/ Board board, /*@ non_null @*/ Color color) {
        super(board, color);
    }

    private boolean canMove(/*@ non_null @*/ Position position) {
        ChessPiece p = (ChessPiece) getBoard().piece(position);
        return p == null || p.getColor() != getColor();
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

        // Movimento em L: 8 direções possíveis
        p.setValues(currentPos.getRow() - 1, currentPos.getCol() - 2);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        p.setValues(currentPos.getRow() - 2, currentPos.getCol() - 1);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        p.setValues(currentPos.getRow() - 2, currentPos.getCol() + 1);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        p.setValues(currentPos.getRow() - 1, currentPos.getCol() + 2);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        p.setValues(currentPos.getRow() + 1, currentPos.getCol() + 2);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        p.setValues(currentPos.getRow() + 2, currentPos.getCol() + 1);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        p.setValues(currentPos.getRow() + 2, currentPos.getCol() - 1);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        p.setValues(currentPos.getRow() + 1, currentPos.getCol() - 2);
        if (board.positionExists(p) && canMove(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        return mat;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("N");
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "N";
    }
}
