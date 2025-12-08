package chess;

import boardgame.BoardException;

public class ChessException extends BoardException {

    /*@ public normal_behavior
      @   requires message != null;
      @*/
    public ChessException(String message) {
        super(message);
    }
}
