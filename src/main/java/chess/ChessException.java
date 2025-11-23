package chess;

import boardgame.BoardException;

public class ChessException extends BoardException {

    //@ assigns \nothing;
    public ChessException(String message) {
        super(message);
    }
}
