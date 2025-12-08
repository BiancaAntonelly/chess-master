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
    //@ public invariant position != null; // ChessPiece sempre tem posição

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   ensures getBoard() == board;
      @   ensures getColor() == color;
      @   ensures getMoveCount() == 0;
      @*/
    public ChessPiece(/*@ non_null @*/ Board board, /*@ non_null @*/ Color color) {
        super(board);
        this.color = color;
        this.moveCount = 0;
        // `position` começa null e será ajustada quando a peça for colocada no tabuleiro
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
      @   requires position != null;
      @   requires position.getRow() >= 0 && position.getRow() < 8;
      @   requires position.getCol() >= 0 && position.getCol() < 8;
      @   ensures \result != null;
      @   ensures \result.getRow() == 8 - position.getRow();
      @   ensures \result.getCol() == (char)('a' + position.getCol());
      @   ensures \result.getRow() >= 1 && \result.getRow() <= 8;
      @   ensures \result.getCol() >= 'a' && \result.getCol() <= 'h';
      @*/
    public /*@ non_null @*/ ChessPosition getChessPosition() {
        //@ assert position != null;
        int rowCalc = 8 - position.getRow();
        int colCalcInt = 'a' + position.getCol();
        //@ assert rowCalc >= 1 && rowCalc <= 8;
        //@ assert colCalcInt >= 'a' && colCalcInt <= 'h';
        char colCalc = (char) colCalcInt;
        //@ assert colCalc >= 'a' && colCalc <= 'h';
        return new ChessPosition(rowCalc, colCalc);
    }

    /*@ public normal_behavior
      @   requires position != null;
      @   requires getBoard() != null;
      @   requires getBoard().positionExists(position);
      @   ensures \result ==> (
      @              getBoard().piece(position) != null
      @          &&  getBoard().piece(position) instanceof ChessPiece
      @          && ((ChessPiece)getBoard().piece(position)).getColor() != color);
      @   ensures !\result ==> (
      @              getBoard().piece(position) == null
      @          ||  !(getBoard().piece(position) instanceof ChessPiece)
      @          || ((ChessPiece)getBoard().piece(position)).getColor() == color);
      @   assignable \nothing;
      @*/
    protected /*@ pure @*/ boolean isThereOpponentPiece(/*@ non_null @*/ Position position) {
        //@ assert color != null;
        Piece p = getBoard().piece(position);
        if (p == null) {
            return false;
        }
        if (!(p instanceof ChessPiece)) {
            return false;
        }
        return ((ChessPiece) p).getColor() != color;
    }

    // Método abstrato - especificações estão nas implementações concretas
    public abstract boolean[][] possibleMoves();

    /*@ also
      @ public normal_behavior
      @   requires position != null;
      @   requires position.getRow() >= 0 && position.getRow() < getBoard().getRows();
      @   requires position.getCol() >= 0 && position.getCol() < getBoard().getCols();
      @   requires this.position != null;
      @   requires possibleMoves() != null;
      @   requires possibleMoves().length == getBoard().getRows();
      @   requires possibleMoves().length > position.getRow();
      @   requires possibleMoves()[position.getRow()] != null;
      @   requires possibleMoves()[position.getRow()].length == getBoard().getCols();
      @   requires possibleMoves()[position.getRow()].length > position.getCol();
      @   ensures \result == possibleMoves()[position.getRow()][position.getCol()];
      @   assignable \nothing;
      @*/
    public boolean possibleMove(/*@ non_null @*/ Position position) {
        return possibleMoves()[position.getRow()][position.getCol()];
    }

    /*@ also
      @ public normal_behavior
      @   requires position != null;
      @   requires getBoard() != null;
      @   requires possibleMoves() != null;
      @   requires possibleMoves().length == getBoard().getRows();
      @   requires getBoard().getRows() > 0;
      @   requires getBoard().getCols() > 0;
      @   requires (\forall int i; 0 <= i && i < getBoard().getRows(); 
      @               possibleMoves()[i] != null && 
      @               possibleMoves()[i].length == getBoard().getCols());
      @   ensures \result == true ==> (\exists int i, j;
      @                  0 <= i && i < getBoard().getRows() &&
      @                  0 <= j && j < getBoard().getCols();
      @                  possibleMoves()[i][j]);
      @   ensures \result == false ==> (\forall int i, j;
      @                  0 <= i && i < getBoard().getRows() &&
      @                  0 <= j && j < getBoard().getCols();
      @                  !possibleMoves()[i][j]);
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean isThereAnyPossibleMove() {
        //@ assert position != null;
        //@ assert getBoard() != null;
        boolean[][] mat = possibleMoves();
        //@ assert mat != null;
        //@ assert mat.length == getBoard().getRows();
        int rows = getBoard().getRows();
        int cols = getBoard().getCols();
        //@ assert rows > 0 && cols > 0;
        /*@ loop_invariant 0 <= i && i <= rows;
          @ loop_invariant mat != null && mat.length == rows;
          @ loop_invariant (\forall int k; 0 <= k && k < i; 
          @                   mat[k] != null && mat[k].length == cols);
          @ loop_invariant (\forall int k, l; 0 <= k && k < i && 0 <= l && l < cols; !mat[k][l]);
          @ decreases rows - i;
          @*/
        for (int i = 0; i < rows; i++) {
            //@ assert mat[i] != null && mat[i].length == cols;
            /*@ loop_invariant 0 <= j && j <= cols;
              @ loop_invariant mat[i] != null && mat[i].length == cols;
              @ loop_invariant (\forall int l; 0 <= l && l < j; !mat[i][l]);
              @ decreases cols - j;
              @*/
            for (int j = 0; j < cols; j++) {
                if (mat[i][j]) {
                    //@ assert (\exists int k, l; 0 <= k && k < rows && 0 <= l && l < cols; mat[k][l]);
                    return true;
                }
            }
        }
        //@ assert (\forall int k, l; 0 <= k && k < rows && 0 <= l && l < cols; !mat[k][l]);
        return false;
    }
}
