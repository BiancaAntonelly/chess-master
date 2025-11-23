package boardgame;

public class BoardException extends RuntimeException {
    //@ assignable \nothing;
    public BoardException(String message) {
        super(message);
    }
}
