package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessPiece;
import chess.Color;

public class Queen extends ChessPiece {

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getMoveCount() == 0;
      @   ensures getBoard() == board;
      @*/
    public Queen(/*@ non_null @*/ Board board, /*@ non_null @*/ Color color) {
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

        // Para cima (Norte)
        if (currentPos.getRow() > 0) {
            p.setValues(currentPos.getRow() - 1, currentPos.getCol());
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
                if (p.getRow() <= 0) break;
                int newRow = p.getRow() - 1;
                if (newRow < 0) break;
                p.setRow(newRow);
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

        // Para esquerda (Oeste)
        if (currentPos.getCol() > 0) {
            p.setValues(currentPos.getRow(), currentPos.getCol() - 1);
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
                if (p.getCol() <= 0) break;
                int newCol = p.getCol() - 1;
                if (newCol < 0) break;
                p.setCol(newCol);
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

        // Para direita (Leste)
        if (currentPos.getCol() < 7) {
            p.setValues(currentPos.getRow(), currentPos.getCol() + 1);
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
                if (p.getCol() >= 7) break;
                int newCol = p.getCol() + 1;
                if (newCol < 0 || newCol >= cols) break;
                p.setCol(newCol);
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

        // Para baixo (Sul)
        if (currentPos.getRow() < 7) {
            p.setValues(currentPos.getRow() + 1, currentPos.getCol());
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
                if (p.getRow() >= 7) break;
                int newRow = p.getRow() + 1;
                if (newRow < 0 || newRow >= rows) break;
                p.setRow(newRow);
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

        // Noroeste (NW)
        p.setValues(currentPos.getRow() - 1, currentPos.getCol() - 1);
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
            int newRow = p.getRow() - 1;
            int newCol = p.getCol() - 1;
            if (newRow < 0 || newCol < 0) break;
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

        // Nordeste (NE)
        p.setValues(currentPos.getRow() - 1, currentPos.getCol() + 1);
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
            int newRow = p.getRow() - 1;
            int newCol = p.getCol() + 1;
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

        // Sudeste (SE)
        p.setValues(currentPos.getRow() + 1, currentPos.getCol() + 1);
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
            int newRow = p.getRow() + 1;
            int newCol = p.getCol() + 1;
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

        // Sudoeste (SW)
        p.setValues(currentPos.getRow() + 1, currentPos.getCol() - 1);
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
            int newRow = p.getRow() + 1;
            int newCol = p.getCol() - 1;
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

        return mat;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("Q");
      @   assignable \nothing;
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "Q";
    }
}
