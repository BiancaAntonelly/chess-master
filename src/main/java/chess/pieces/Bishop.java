package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessPiece;
import chess.Color;

public class Bishop extends ChessPiece {

    public Bishop(Board board, Color color) {
        super(board, color);
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

        // Noroeste (NW) - diagonal superior esquerda
        int rowNW = currentPos.getRow();
        int colNW = currentPos.getCol();
        if (rowNW > 0 && colNW > 0) {
            p.setValues(rowNW - 1, colNW - 1);
            while (board.positionExists(p) && !board.isPiecePlaced(p)) {
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
                int currentRow = p.getRow();
                int currentCol = p.getCol();
                if (currentRow <= 0 || currentCol <= 0) break;
                int newRow = currentRow - 1;
                int newCol = currentCol - 1;
                if (newRow < 0 || newCol < 0 || newRow >= rows || newCol >= cols) break;
                p.setValues(newRow, newCol);
            }
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
        }

        // Nordeste (NE) - diagonal superior direita
        int rowNE = currentPos.getRow();
        int colNE = currentPos.getCol();
        if (rowNE > 0 && colNE < cols - 1) {
            p.setValues(rowNE - 1, colNE + 1);
            while (board.positionExists(p) && !board.isPiecePlaced(p)) {
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
                int currentRow = p.getRow();
                int currentCol = p.getCol();
                if (currentRow <= 0 || currentCol >= cols - 1) break;
                int newRow = currentRow - 1;
                int newCol = currentCol + 1;
                if (newRow < 0 || newCol < 0 || newRow >= rows || newCol >= cols) break;
                p.setValues(newRow, newCol);
            }
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
        }

        // Sudeste (SE) - diagonal inferior direita
        int rowSE = currentPos.getRow();
        int colSE = currentPos.getCol();
        if (rowSE < rows - 1 && colSE < cols - 1) {
            p.setValues(rowSE + 1, colSE + 1);
            while (board.positionExists(p) && !board.isPiecePlaced(p)) {
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
                int currentRow = p.getRow();
                int currentCol = p.getCol();
                if (currentRow >= rows - 1 || currentCol >= cols - 1) break;
                int newRow = currentRow + 1;
                int newCol = currentCol + 1;
                if (newRow < 0 || newCol < 0 || newRow >= rows || newCol >= cols) break;
                p.setValues(newRow, newCol);
            }
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
        }

        // Sudoeste (SW) - diagonal inferior esquerda
        int rowSW = currentPos.getRow();
        int colSW = currentPos.getCol();
        if (rowSW < rows - 1 && colSW > 0) {
            p.setValues(rowSW + 1, colSW - 1);
            while (board.positionExists(p) && !board.isPiecePlaced(p)) {
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
                int currentRow = p.getRow();
                int currentCol = p.getCol();
                if (currentRow >= rows - 1 || currentCol <= 0) break;
                int newRow = currentRow + 1;
                int newCol = currentCol - 1;
                if (newRow < 0 || newCol < 0 || newRow >= rows || newCol >= cols) break;
                p.setValues(newRow, newCol);
            }
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
