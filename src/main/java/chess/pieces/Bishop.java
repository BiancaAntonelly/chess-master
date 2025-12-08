package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessPiece;
import chess.Color;

public class Bishop extends ChessPiece {

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getColor() == color;
      @   ensures getMoveCount() == 0;
      @   ensures getBoard() == board;
      @*/
    public Bishop(/*@ non_null @*/ Board board, /*@ non_null @*/ Color color) {
        super(board, color);
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

        // Noroeste (NW) - diagonal superior esquerda
        p.setValues(currentPos.getRow() - 1, currentPos.getCol() - 1);
        while (board.positionExists(p) && !board.isPiecePlaced(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
            int newRow = p.getRow() - 1;
            int newCol = p.getCol() - 1;
            if (newRow < 0 || newCol < 0) break;
            p.setValues(newRow, newCol);
        }
        if (board.positionExists(p) && isThereOpponentPiece(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // Nordeste (NE) - diagonal superior direita
        p.setValues(currentPos.getRow() - 1, currentPos.getCol() + 1);
        while (board.positionExists(p) && !board.isPiecePlaced(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
            int newRow = p.getRow() - 1;
            int newCol = p.getCol() + 1;
            if (newRow < 0 || newCol >= mat.length) break;
            p.setValues(newRow, newCol);
        }
        if (board.positionExists(p) && isThereOpponentPiece(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // Sudeste (SE) - diagonal inferior direita
        p.setValues(currentPos.getRow() + 1, currentPos.getCol() + 1);
        while (board.positionExists(p) && !board.isPiecePlaced(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
            int newRow = p.getRow() + 1;
            int newCol = p.getCol() + 1;
            if (newRow >= mat.length || newCol >= mat.length) break;
            p.setValues(newRow, newCol);
        }
        if (board.positionExists(p) && isThereOpponentPiece(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // Sudoeste (SW) - diagonal inferior esquerda
        p.setValues(currentPos.getRow() + 1, currentPos.getCol() - 1);
        while (board.positionExists(p) && !board.isPiecePlaced(p)) {
            int r = p.getRow();
            int c = p.getCol();
            if (r >= 0 && r < mat.length) {
                if (c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
            int newRow = p.getRow() + 1;
            int newCol = p.getCol() - 1;
            if (newRow >= mat.length || newCol < 0) break;
            p.setValues(newRow, newCol);
        }
        if (board.positionExists(p) && isThereOpponentPiece(p)) {
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
      @   ensures \result.equals("B");
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "B";
    }
}
