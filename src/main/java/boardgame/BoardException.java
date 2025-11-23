package boardgame;

public class BoardException extends RuntimeException {

    /*@ public normal_behavior
      @   assignable \nothing;
      @*/
    public BoardException(String message) {
        super(message);
    }
}
