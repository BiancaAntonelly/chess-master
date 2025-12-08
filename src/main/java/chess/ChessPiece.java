package chess;

import boardgame.Board;
import boardgame.Piece;
import boardgame.Position;

public abstract class ChessPiece extends Piece {

    //@ spec_public
    private /*@ non_null @*/ Color color;

    //@ spec_public
    private int moveCount;

    //@ public invariant color != null;

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getBoard() == board;
      @   ensures getColor() == color;
      @   ensures getMoveCount() == 0;
      @   ensures position == null;
      @*/
    public ChessPiece(/*@ non_null @*/ Board board, /*@ non_null @*/ Color color) {
        super(board);
        this.color = color;
        this.moveCount = 0;
    }

    /*@ public normal_behavior
      @   ensures \result != null;
      @   ensures \result == color;
      @   assignable \nothing;
      @*/
    public /*@ pure non_null @*/ Color getColor() {
        return color;
    }

    /*@ public normal_behavior
      @   ensures \result == moveCount;
      @   ensures \result >= 0;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getMoveCount() {
        return moveCount;
    }

    /*@ public normal_behavior
      @   requires moveCount < Integer.MAX_VALUE;
      @   ensures moveCount == \old(moveCount) + 1;
      @   assignable moveCount;
      @*/
    protected void increaseMoveCount() {
        moveCount++;
    }

    /*@ public normal_behavior
      @   requires moveCount > 0;
      @   ensures moveCount == \old(moveCount) - 1;
      @   assignable moveCount;
      @*/
    protected void decreaseMoveCount() {
        moveCount--;
    }

    public ChessPosition getChessPosition() {
        if (position == null) {
            throw new IllegalStateException("Position is null");
        }
        if (position.getRow() < 0 || position.getRow() >= 8 || 
            position.getCol() < 0 || position.getCol() >= 8) {
            throw new IllegalStateException("Invalid position");
        }
        int rowCalc = 8 - position.getRow();
        int colCalcInt = 'a' + position.getCol();
        char colCalc = (char) colCalcInt;
        return new ChessPosition(rowCalc, colCalc);
    }

    protected boolean isThereOpponentPiece(Position position) {
        if (position == null || getBoard() == null) {
            return false;
        }
        if (!getBoard().positionExists(position)) {
            return false;
        }
        Piece p = getBoard().piece(position);
        if (p == null) {
            return false;
        }
        if (!(p instanceof ChessPiece)) {
            return false;
        }
        ChessPiece cp = (ChessPiece) p;
        Color cpColor = cp.getColor();
        if (cpColor == null || this.color == null) {
            return false;
        }
        return cpColor != this.color;
    }

    // Método abstrato - especificações estão nas implementações concretas
    public abstract boolean[][] possibleMoves();

    /*@ also
      @ public normal_behavior
      @   requires position != null;
      @   requires this.position != null;
      @   requires getBoard() != null;
      @   requires position.getRow() >= 0 && position.getRow() < getBoard().getRows();
      @   requires position.getCol() >= 0 && position.getCol() < getBoard().getCols();
      @   requires possibleMoves() != null;
      @   requires possibleMoves().length == getBoard().getRows();
      @   requires possibleMoves().length > position.getRow();
      @   requires possibleMoves()[position.getRow()] != null;
      @   requires possibleMoves()[position.getRow()].length == getBoard().getCols();
      @   requires possibleMoves()[position.getRow()].length > position.getCol();
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean possibleMove(/*@ non_null @*/ Position position) {
        boolean[][] moves = possibleMoves();
        return moves[position.getRow()][position.getCol()];
    }

    public boolean isThereAnyPossibleMove() {
        if (position == null || getBoard() == null) {
            return false;
        }
        boolean[][] mat = possibleMoves();
        if (mat == null) {
            return false;
        }
        int rows = getBoard().getRows();
        int cols = getBoard().getCols();
        if (rows <= 0 || cols <= 0 || rows > mat.length) {
            return false;
        }
        for (int i = 0; i < rows && i < mat.length && i >= 0; i++) {
            if (mat[i] == null || mat[i].length != cols) {
                continue;
            }
            boolean[] row = mat[i];
            if (row == null) {
                continue;
            }
            for (int j = 0; j < cols && j < row.length && j >= 0; j++) {
                if (row[j]) {
                    return true;
                }
            }
        }
        return false;
    }
}
