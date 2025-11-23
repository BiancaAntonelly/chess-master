package chess;

import boardgame.Board;
import boardgame.Piece;
import boardgame.Position;

public abstract class ChessPiece extends Piece {

    //@ spec_public
    private final Color color;

    //@ spec_public
    private int moveCount;

    public ChessPiece(Board board, Color color) {
        super(board);
        this.color = color;
    }

    /*@ public normal_behavior
      @ ensures \result == color;
      @ pure
      @*/
    public Color getColor() {
        return color;
    }

    /*@ public normal_behavior
      @ ensures \result == moveCount;
      @ pure
      @*/
    public int getMoveCount() {
        return moveCount;
    }

    /*@ public normal_behavior
      @ ensures moveCount == \old(moveCount) + 1;
      @ assignable moveCount;
      @*/
    public void increaseMoveCount() {
        moveCount++;
    }

    /*@ public normal_behavior
      @ requires moveCount > 0;
      @ ensures moveCount == \old(moveCount) - 1;
      @ assignable moveCount;
      @*/
    public void decreaseMoveCount() {
        moveCount--;
    }

    /*@ public normal_behavior
      @ requires position != null;
      @ ensures \result.getRow() == 8 - position.getRow();
      @ ensures \result.getCol() == (char)('a' + position.getCol());
      @ pure
      @*/
    public ChessPosition getChessPosition() {
        return ChessPosition.fromPosition(position);
    }

    /*@ public normal_behavior
      @ requires position != null;
      @ requires board != null;
      @ requires board.positionExists(pos);
      @ ensures \result ==> (board.piece(pos) != null);
      @ pure
      @*/
    public boolean isThereOpponentPiece(Position pos) {
        ChessPiece p = (ChessPiece) getBoard().piece(pos);
        return p != null && p.getColor() != color;
    }
}
