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
    //@ public invariant moveCount >= 0;
    //@ public invariant moveCount <= Integer.MAX_VALUE;

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

    /*@ public normal_behavior
      @   requires this.position != null;
      @   requires this.position.getRow() >= 0 && this.position.getRow() < 8;
      @   requires this.position.getCol() >= 0 && this.position.getCol() < 8;
      @   requires this.color != null;
      @   requires this.moveCount >= 0 && this.moveCount <= Integer.MAX_VALUE;
      @   requires getBoard() != null;
      @   ensures \result != null;
      @   assignable \nothing;
      @*/
    public /*@ non_null @*/ ChessPosition getChessPosition() {
        if (position == null) {
            throw new IllegalStateException("Position is null");
        }
        int rowCalc = 8 - position.getRow();
        int colCalcInt = 'a' + position.getCol();
        char colCalc = (char) colCalcInt;
        return new ChessPosition(rowCalc, colCalc);
    }

    /*@ public normal_behavior
      @   requires position != null;
      @   requires getBoard() != null;
      @   requires getBoard().positionExists(position);
      @   assignable \nothing;
      @*/
    protected boolean isThereOpponentPiece(/*@ non_null @*/ Position position) {
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

    /*@ also
      @ public normal_behavior
      @   requires this.position != null;
      @   requires getBoard() != null;
      @   requires possibleMoves() != null;
      @   requires possibleMoves().length == getBoard().getRows();
      @   requires getBoard().getRows() > 0;
      @   requires getBoard().getCols() > 0;
      @   requires (\forall int i; 0 <= i && i < getBoard().getRows(); 
      @               possibleMoves()[i] != null && 
      @               possibleMoves()[i].length == getBoard().getCols());
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean isThereAnyPossibleMove() {
        boolean[][] mat = possibleMoves();
        int rows = getBoard().getRows();
        int cols = getBoard().getCols();
        /*@ loop_invariant 0 <= i && i <= rows;
          @ decreases rows - i;
          @*/
        for (int i = 0; i < rows; i++) {
            if (mat[i] == null || mat[i].length != cols) {
                continue;
            }
            boolean[] row = mat[i];
            /*@ loop_invariant 0 <= j && j <= cols;
              @ loop_invariant row != null && row.length == cols;
              @ decreases cols - j;
              @*/
            for (int j = 0; j < cols; j++) {
                if (row[j]) {
                    return true;
                }
            }
        }
        return false;
    }
}
