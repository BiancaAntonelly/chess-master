package chess;

import boardgame.Board;
import boardgame.Piece;
import boardgame.Position;

public abstract class ChessPiece extends Piece {

    //@ public invariant color != null;
    //@ public invariant moveCount >= 0;

    //@ spec_public
    private final Color color;

    //@ spec_public
    private int moveCount;

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @*/
    public ChessPiece(Board board, Color color) {
        super(board);
        this.color = color;
    }

    /*@ pure @*/
    public Color getColor() {
        return color;
    }

    /*@ pure @*/
    public int getMoveCount() {
        return moveCount;
    }

    /*@ public normal_behavior
      @   requires moveCount < Integer.MAX_VALUE;
      @   assignable moveCount;
      @*/
    public void increaseMoveCount() {
        moveCount++;
    }

    /*@ public normal_behavior
      @   requires moveCount > 0;
      @   assignable moveCount;
      @*/
    public void decreaseMoveCount() {
        moveCount--;
    }

    /*@ public normal_behavior
      @   requires position != null;
      @   requires position.getRow() >= 0 && position.getRow() < 8;
      @   requires position.getCol() >= 0 && position.getCol() < 8;
      @   assignable \nothing;
      @*/
    public ChessPosition getChessPosition() {
        return ChessPosition.fromPosition(position);
    }

    /*@ public normal_behavior
      @   requires pos != null;
      @   assignable \nothing;
      @*/
    public boolean isThereOpponentPiece(Position pos) {
        ChessPiece p = (ChessPiece) getBoard().piece(pos);
        return p != null && p.getColor() != color;
    }

}
