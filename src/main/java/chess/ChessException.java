package chess;

import boardgame.BoardException;

/**
 * Exceção específica para erros de xadrez.
 * Lançada quando ocorre uma violação de regras do jogo de xadrez.
 */
public class ChessException extends BoardException {

    /*@ public normal_behavior
      @   requires message != null;
      @   ensures getMessage().equals(message);
      @   assignable \nothing;
      @*/
    public ChessException(/*@ non_null @*/ String message) {
        super(message);
    }
}
