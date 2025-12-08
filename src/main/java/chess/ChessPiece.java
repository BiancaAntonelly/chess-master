package chess;

import boardgame.Board;
import boardgame.Piece;
import boardgame.Position;

/**
 * Classe base para peças de xadrez.
 */
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
      @   assignable modelBoard, this.color, moveCount, position;
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
      @   ensures \result != null;
      @   assignable \nothing;
      @*/
    public /*@ pure non_null @*/ ChessPosition getChessPosition() {
        return new ChessPosition(position.getRow(), (char) ('a' + position.getCol()));
    }

    /*@ public normal_behavior
      @   requires position != null;
      @   ensures \result ==> (
      @              getBoard().piece(position) != null
      @          &&  getBoard().piece(position) instanceof ChessPiece
      @          && ((ChessPiece)getBoard().piece(position)).getColor() != color);
      @   assignable \nothing;
      @*/
    protected boolean isThereOpponentPiece(/*@ non_null @*/ Position position) {
        Piece p = getBoard().piece(position);
        return p != null && p instanceof ChessPiece && ((ChessPiece) p).getColor() != color;
    }

    /*@ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.length == getBoard().getRows();
      @   assignable \nothing;
      @*/
    public abstract boolean[][] possibleMoves();

    /*@ public normal_behavior
      @   requires position != null;
      @   requires position.getRow() >= 0 && position.getRow() < getBoard().getRows();
      @   requires position.getCol() >= 0 && position.getCol() < getBoard().getCols();
      @   ensures \result == possibleMoves()[position.getRow()][position.getCol()];
      @   assignable \nothing;
      @*/
    public boolean possibleMove(/*@ non_null @*/ Position position) {
        return possibleMoves()[position.getRow()][position.getCol()];
    }

    /*@ public normal_behavior
      @   ensures \result ==> (
      @              (\exists int i, j;
      @                  0 <= i && i < getBoard().getRows() &&
      @                  0 <= j && j < getBoard().getCols();
      @                  possibleMoves()[i][j]));
      @   assignable \nothing;
      @*/
    public boolean isThereAnyPossibleMove() {
        boolean[][] mat = possibleMoves();
        for (int i = 0; i < getBoard().getRows(); i++) {
            for (int j = 0; j < getBoard().getCols(); j++) {
                if (mat[i][j]) {
                    return true;
                }
            }
        }
        return false;
    }
}
