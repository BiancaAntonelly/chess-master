package chess;

import boardgame.BoardException;

public class ChessException extends BoardException {

    /*@ public normal_behavior
      @   assignable \nothing;
      @*/
    public ChessException(String message) {
        super(message);
    }
}
