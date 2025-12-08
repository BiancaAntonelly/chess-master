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

        int rows = board.getRows();
        int cols = board.getCols();
        //@ assert rows > 0 && cols > 0;
        boolean[][] mat = new boolean[rows][cols];
        //@ assert mat != null;
        //@ assert mat.length == rows;
        Position p = new Position(0, 0);

        // PARA CIMA
        if (currentPos.getRow() > 0) {
            int startRow = currentPos.getRow() - 1;
            int startCol = currentPos.getCol();
            if (startRow >= 0 && startRow < rows && startCol >= 0 && startCol < cols) {
                p.setValues(startRow, startCol);
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
        }

        // PARA ESQUERDA
        if (currentPos.getCol() > 0) {
            int startRow = currentPos.getRow();
            int startCol = currentPos.getCol() - 1;
            if (startRow >= 0 && startRow < rows && startCol >= 0 && startCol < cols) {
                p.setValues(startRow, startCol);
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
        }

        // PARA DIREITA
        if (currentPos.getCol() < 7) {
            int startRow = currentPos.getRow();
            int startCol = currentPos.getCol() + 1;
            if (startRow >= 0 && startRow < rows && startCol >= 0 && startCol < cols) {
                p.setValues(startRow, startCol);
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
        }

        // PARA BAIXO
        if (currentPos.getRow() < 7) {
            int startRow = currentPos.getRow() + 1;
            int startCol = currentPos.getCol();
            if (startRow >= 0 && startRow < rows && startCol >= 0 && startCol < cols) {
                p.setValues(startRow, startCol);
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
        }

        return mat;
    }
}
