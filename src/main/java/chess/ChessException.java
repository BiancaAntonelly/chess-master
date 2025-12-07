package chess;

import boardgame.BoardException;

public class ChessException extends BoardException {

    /*@ public normal_behavior
      @   ensures getMessage() == message;
      @   assignable \nothing;
      @*/
    public ChessException(String message) {
        super(message);
    }
}
