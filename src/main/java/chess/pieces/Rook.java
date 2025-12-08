package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessPiece;
import chess.Color;

public class Rook extends ChessPiece {

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getMoveCount() == 0;
      @   ensures getBoard() == board;
      @*/
    public Rook(/*@ non_null @*/ Board board, /*@ non_null @*/ Color color) {
        super(board, color);
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("R");
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "R";
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

        boolean[][] mat = new boolean[board.getRows()][board.getCols()];
        Position p = new Position(0, 0);

        // PARA CIMA
        if (currentPos.getRow() > 0) {
            p.setValues(currentPos.getRow() - 1, currentPos.getCol());
            p.setValues(position.getRow() - 1, position.getCol());

            while (board.positionExists(p) && !board.isPiecePlaced(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < mat.length && c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
                if (p.getRow() == 0) break;
                p.setRow(p.getRow() - 1);
            }
            if (board.positionExists(p) && isThereOpponentPiece(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < mat.length && c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // PARA ESQUERDA
        if (currentPos.getCol() > 0) {
            p.setValues(currentPos.getRow(), currentPos.getCol() - 1);

            while (board.positionExists(p) && !board.isPiecePlaced(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < mat.length && c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
                if (p.getCol() == 0) break;
                p.setCol(p.getCol() - 1);
            }
            if (board.positionExists(p) && isThereOpponentPiece(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < mat.length && c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // PARA DIREITA
        if (currentPos.getCol() < 7) {
            p.setValues(currentPos.getRow(), currentPos.getCol() + 1);

            while (board.positionExists(p) && !board.isPiecePlaced(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < mat.length && c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
                if (p.getCol() == 7) break;
                p.setCol(p.getCol() + 1);
            }
            if (board.positionExists(p) && isThereOpponentPiece(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < mat.length && c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        // PARA BAIXO
        if (currentPos.getRow() < 7) {
            p.setValues(currentPos.getRow() + 1, currentPos.getCol());

            while (board.positionExists(p) && !board.isPiecePlaced(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < mat.length && c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
                if (p.getRow() == 7) break;
                p.setRow(p.getRow() + 1);
            }
            if (board.positionExists(p) && isThereOpponentPiece(p)) {
                int r = p.getRow();
                int c = p.getCol();
                if (r >= 0 && r < mat.length && c >= 0 && c < mat[r].length) {
                    mat[r][c] = true;
                }
            }
        }

        return mat;
    }
}
