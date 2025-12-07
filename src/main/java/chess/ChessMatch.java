package chess;

import boardgame.Board;
import boardgame.Piece;
import boardgame.Position;
import chess.pieces.*;

import java.util.ArrayList;
import java.util.List;

/**
 * Classe que representa uma partida de xadrez.
 * Gerencia o estado do jogo, turnos, movimentos e regras do xadrez.
 */
public class ChessMatch {

    //@ public invariant board != null;
    //@ public invariant board.getRows() == 8 && board.getCols() == 8;
    //@ public invariant turn >= 1;
    //@ public invariant currentPlayer != null;
    //@ public invariant piecesOnTheBoard != null;
    //@ public invariant capturedPieces != null;
    //@ public invariant !checkMate ==> (currentPlayer == Color.WHITE || currentPlayer == Color.BLACK);

    //@ spec_public
    protected Board board;
    //@ spec_public
    private int turn;
    //@ spec_public
    private Color currentPlayer;
    //@ spec_public
    private boolean check;
    //@ spec_public
    private boolean checkMate;
    /*@ spec_public @*/ /*@ nullable @*/ private ChessPiece enPassantVulnerable;
    /*@ spec_public @*/ /*@ nullable @*/ private ChessPiece promoted;
    //@ spec_public
    private final List<Piece> piecesOnTheBoard = new ArrayList<>();
    //@ spec_public
    private final List<Piece> capturedPieces = new ArrayList<>();

    /*@ public normal_behavior
      @   ensures board != null;
      @   ensures board.getRows() == 8 && board.getCols() == 8;
      @   ensures turn == 1;
      @   ensures currentPlayer == Color.WHITE;
      @   ensures !check;
      @   ensures !checkMate;
      @   ensures enPassantVulnerable == null;
      @   ensures promoted == null;
      @   ensures piecesOnTheBoard != null;
      @   ensures capturedPieces != null;
      @*/
    public ChessMatch() {
        board = new Board(8, 8);
        turn = 1;
        currentPlayer = Color.WHITE;
        check = false;
        checkMate = false;
        enPassantVulnerable = null;
        promoted = null;
        initialSetup();
    }

    /*@ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.length == board.getRows();
      @   ensures (\forall int i; 0 <= i && i < board.getRows();
      @               \result[i] != null && \result[i].length == board.getCols());
      @   assignable \nothing;
      @*/
    public ChessPiece[][] getPieces() {
        final int rows = board.getRows();
        final int cols = board.getCols();
        ChessPiece[][] mat = new ChessPiece[rows][cols];

        /*@ loop_invariant 0 <= i && i <= rows;
          @ loop_invariant (\forall int r; 0 <= r && r < i;
          @                     (\forall int c; 0 <= c && c < cols;
          @                         mat[r][c] == null
          @                          || mat[r][c] instanceof ChessPiece));
          @ decreases rows - i;
          @*/
        for (int i = 0; i < rows; i++) {

            /*@ loop_invariant 0 <= j && j <= cols;
              @ loop_invariant (\forall int c; 0 <= c && c < j;
              @                     mat[i][c] == null
              @                      || mat[i][c] instanceof ChessPiece);
              @ decreases cols - j;
              @*/
            for (int j = 0; j < cols; j++) {
                //@ assert 0 <= i && i < rows;
                //@ assert 0 <= j && j < cols;

                /*@ nullable @*/ Piece p = board.piece(i, j);

                if (p instanceof ChessPiece) {
                    mat[i][j] = (ChessPiece) p;
                } else {
                    mat[i][j] = null;
                }
            }
        }
        return mat;
    }

    /*@ public normal_behavior
      @   ensures \result == turn;
      @   ensures \result >= 1;
      @   assignable \nothing;
      @   pure
      @*/
    public int getTurn() {
        return turn;
    }

    /*@ public normal_behavior
      @   ensures \result == currentPlayer;
      @   ensures \result != null;
      @   assignable \nothing;
      @   pure
      @*/
    public Color getCurrentPlayer() {
        return currentPlayer;
    }

    /*@ public normal_behavior
      @   ensures \result == check;
      @   assignable \nothing;
      @   pure
      @*/
    public boolean getCheck() {
        return check;
    }

    /*@ public normal_behavior
      @   ensures \result == !checkMate;
      @   assignable \nothing;
      @   pure
      @*/
    public boolean getNotCheckMate() {
        return !checkMate;
    }

    /*@ public normal_behavior
      @   ensures \result == enPassantVulnerable;
      @   assignable \nothing;
      @   pure
      @*/
    public /*@ nullable @*/ ChessPiece getEnPassantVulnerable() {
        return enPassantVulnerable;
    }

    /*@ public normal_behavior
      @   ensures \result == promoted;
      @   assignable \nothing;
      @   pure
      @*/
    public /*@ nullable @*/ ChessPiece getPromoted() {
        return promoted;
    }

    /*@ public normal_behavior
      @   requires sourcePos != null;
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8;
      @               \result[i] != null && \result[i].length == 8);
      @   assignable \nothing;
      @ also public exceptional_behavior
      @   requires sourcePos != null;
      @   assignable \nothing;
      @   signals_only ChessException;
      @*/
    public boolean[][] possibleMoves(ChessPosition sourcePos) {
        Position position = sourcePos.toPosition();
        validateSourcePosition(position);
        return board.piece(position).possibleMoves();
    }

    /*@ public normal_behavior
      @   requires sourcePos != null && targetPos != null;
      @   ensures turn >= \old(turn);
      @   ensures currentPlayer != null;
      @   assignable board, turn, currentPlayer, check, checkMate,
      @              enPassantVulnerable, promoted, piecesOnTheBoard, capturedPieces;
      @ also public exceptional_behavior
      @   requires sourcePos != null && targetPos != null;
      @   assignable board, turn, currentPlayer, check, checkMate,
      @              enPassantVulnerable, promoted, piecesOnTheBoard, capturedPieces;
      @   signals_only ChessException;
      @*/
    public ChessPiece performChessMove(ChessPosition sourcePos, ChessPosition targetPos) {
        Position source = sourcePos.toPosition();
        Position target = targetPos.toPosition();
        validateSourcePosition(source);
        validateTargetPosition(source, target);
        Piece captured = makeMove(source, target);

        if (testCheck(currentPlayer)) {
            undoMove(source, target, captured);
            throw new ChessException("Você não pode se colocar em xeque.");
        }
        ChessPiece moved = (ChessPiece) board.piece(target);

        // Promoção
        promoted = null;
        if (moved instanceof Pawn) {
            if ((moved.getColor() == Color.WHITE && target.getRow() == 0)
                    || (moved.getColor() == Color.BLACK && target.getRow() == 7)) {
                promoted = (ChessPiece) board.piece(target);
                promoted = replacePromotedPiece("Q");
            }
        }

        check = testCheck(opponent(currentPlayer));
        if (testCheckMate(opponent(currentPlayer))) {
            checkMate = true;
        } else {
            nextTurn();
        }

        // En Passant
        if (moved instanceof Pawn &&
                (target.getRow() == source.getRow() - 2 || target.getRow() == source.getRow() + 2)) {
            enPassantVulnerable = moved;
        } else {
            enPassantVulnerable = null;
        }

        return (ChessPiece) captured;
    }

    /*@ public normal_behavior
      @   requires type != null;
      @   requires promoted != null;
      @   ensures \result != null;
      @   assignable board, piecesOnTheBoard, promoted;
      @ also public exceptional_behavior
      @   requires promoted == null;
      @   assignable \nothing;
      @   signals_only IllegalStateException;
      @*/
    public ChessPiece replacePromotedPiece(String type) {
        if (promoted == null) {
            throw new IllegalStateException("Não há peça para ser promovida");
        }
        if (!type.equals("B") && !type.equals("N") && !type.equals("R") && !type.equals("Q")) {
            return promoted;
        }

        Position pos = promoted.getChessPosition().toPosition();
        Piece p = board.removePiece(pos);
        piecesOnTheBoard.remove(p);

        ChessPiece newPiece = newPiece(type, promoted.getColor());
        board.placePiece(newPiece, pos);
        piecesOnTheBoard.add(newPiece);
        promoted = newPiece;
        return newPiece;
    }

    /*@ private normal_behavior
      @   requires type != null;
      @   requires color != null;
      @   ensures \result != null;
      @   assignable \nothing;
      @*/
    private ChessPiece newPiece(String type, Color color) {
        return switch (type) {
            case "B" -> new Bishop(board, color);
            case "N" -> new Knight(board, color);
            case "Q" -> new Queen(board, color);
            default -> new Rook(board, color);
        };
    }

    /*@ private normal_behavior
      @   requires source != null && target != null;
      @   assignable board, piecesOnTheBoard, capturedPieces;
      @*/
    private Piece makeMove(Position source, Position target) {
        ChessPiece p = (ChessPiece) board.removePiece(source);
        p.increaseMoveCount();
        Piece captured = board.removePiece(target);
        board.placePiece(p, target);

        if (captured != null) {
            piecesOnTheBoard.remove(captured);
            capturedPieces.add(captured);
        }
        // Roque pequeno
        if (p instanceof King && target.getCol() == source.getCol() + 2) {
            Position sourceT = new Position(source.getRow(), source.getCol() + 3);
            Position targetT = new Position(source.getRow(), source.getCol() + 1);
            ChessPiece rook = (ChessPiece) board.removePiece(sourceT);
            board.placePiece(rook, targetT);
            rook.increaseMoveCount();
        }
        // Roque grande
        if (p instanceof King && target.getCol() == source.getCol() - 2) {
            Position sourceT = new Position(source.getRow(), source.getCol() - 4);
            Position targetT = new Position(source.getRow(), source.getCol() - 1);
            ChessPiece rook = (ChessPiece) board.removePiece(sourceT);
            board.placePiece(rook, targetT);
            rook.increaseMoveCount();
        }
        // En Passant
        if (p instanceof Pawn) {
            if (source.getCol() != target.getCol() && captured == null) {
                Position pawnPosition = new Position(
                        p.getColor() == Color.WHITE ? target.getRow() + 1 : target.getRow() - 1,
                        target.getCol());
                captured = board.removePiece(pawnPosition);
                capturedPieces.add(captured);
                piecesOnTheBoard.remove(captured);
            }
        }

        return captured;
    }

    /*@ private normal_behavior
      @   requires source != null && target != null;
      @   assignable board, piecesOnTheBoard, capturedPieces;
      @*/
    private void undoMove(Position source, Position target, Piece captured) {
        ChessPiece p = (ChessPiece) board.removePiece(target);
        p.decreaseMoveCount();
        board.placePiece(p, source);

        if (captured != null) {
            board.placePiece(captured, target);
        }
        // Roque pequeno
        if (p instanceof King && target.getCol() == source.getCol() + 2) {
            Position sourceT = new Position(source.getRow(), source.getCol() + 3);
            Position targetT = new Position(source.getRow(), source.getCol() + 1);
            ChessPiece rook = (ChessPiece) board.removePiece(targetT);
            board.placePiece(rook, sourceT);
            rook.decreaseMoveCount();
        }
        // Roque grande
        if (p instanceof King && target.getCol() == source.getCol() - 2) {
            Position sourceT = new Position(source.getRow(), source.getCol() - 4);
            Position targetT = new Position(source.getRow(), source.getCol() - 1);
            ChessPiece rook = (ChessPiece) board.removePiece(targetT);
            board.placePiece(rook, sourceT);
            rook.decreaseMoveCount();
        }
        // En Passant
        if (p instanceof Pawn) {
            if (source.getCol() != target.getCol() && captured == enPassantVulnerable) {
                ChessPiece pawn = (ChessPiece) board.removePiece(target);
                Position pawnPosition = new Position(
                        p.getColor() == Color.WHITE ? 3 : 4,
                        target.getCol());
                board.placePiece(pawn, pawnPosition);
            }
        }

        capturedPieces.remove(captured);
        if (captured != null) {
            piecesOnTheBoard.add(captured);
        }
    }

    /*@ private normal_behavior
      @   requires pos != null;
      @   assignable \nothing;
      @ also private exceptional_behavior
      @   requires pos != null;
      @   assignable \nothing;
      @   signals_only ChessException;
      @*/
    private void validateSourcePosition(Position pos) {
        if (!board.isPiecePlaced(pos)) {
            throw new ChessException("Não existe peça na posição de origem.");
        }
        if (currentPlayer != ((ChessPiece) board.piece(pos)).getColor()) {
            throw new ChessException("A peça escolhida não é sua.");
        }
        if (!board.piece(pos).isThereAnyPossibleMove()) {
            throw new ChessException("Não existe movimentos possíveis para a peça escolhida.");
        }
    }

    /*@ private normal_behavior
      @   requires source != null && target != null;
      @   assignable \nothing;
      @ also private exceptional_behavior
      @   requires source != null && target != null;
      @   assignable \nothing;
      @   signals_only ChessException;
      @*/
    private void validateTargetPosition(Position source, Position target) {
        if (!board.piece(source).possibleMove(target)) {
            throw new ChessException("A peça escolhida não pode realizar esse movimento.");
        }
    }

    /*@ private normal_behavior
      @   requires turn < Integer.MAX_VALUE;
      @   ensures turn == \old(turn) + 1;
      @   ensures currentPlayer == (\old(currentPlayer) == Color.WHITE ? Color.BLACK : Color.WHITE);
      @   assignable turn, currentPlayer;
      @*/
    private void nextTurn() {
        turn++;
        currentPlayer = (currentPlayer == Color.WHITE) ? Color.BLACK : Color.WHITE;
    }

    /*@ private normal_behavior
      @   requires color != null;
      @   ensures \result != null;
      @   ensures \result == (color == Color.WHITE ? Color.BLACK : Color.WHITE);
      @   assignable \nothing;
      @   pure
      @*/
    private Color opponent(Color color) {
        return color == Color.WHITE ? Color.BLACK : Color.WHITE;
    }

    /*@ private normal_behavior
      @   requires color != null;
      @   ensures \result != null;
      @   ensures \result instanceof King;
      @   assignable \nothing;
      @ also private exceptional_behavior
      @   requires color != null;
      @   assignable \nothing;
      @   signals_only IllegalStateException;
      @*/
    private ChessPiece king(Color color) {
        List<Piece> list = piecesOnTheBoard.stream()
                .filter(x -> x != null && ((ChessPiece) x).getColor() == color)
                .toList();
        for (Piece p : list) {
            if (p instanceof King) {
                return (ChessPiece) p;
            }
        }
        throw new IllegalStateException("Não existe um rei " + color + " no tabuleiro.");
    }

    /*@ private normal_behavior
      @   requires color != null;
      @   assignable \nothing;
      @*/
    private boolean testCheck(Color color) {
        Position kingPos = king(color).getChessPosition().toPosition();
        List<Piece> opponentPieces = piecesOnTheBoard.stream()
                .filter(x -> x != null && ((ChessPiece) x).getColor() == opponent(color))
                .toList();
        for (Piece p : opponentPieces) {
            boolean[][] mat = p.possibleMoves();
            if (mat[kingPos.getRow()][kingPos.getCol()]) {
                return true;
            }
        }
        return false;
    }

    /*@ private normal_behavior
      @   requires color != null;
      @   assignable board, piecesOnTheBoard, capturedPieces;
      @*/
    private boolean testCheckMate(Color color) {
        if (!testCheck(color)) return false;

        List<Piece> list = piecesOnTheBoard.stream()
                .filter(x -> x != null && ((ChessPiece) x).getColor() == color)
                .toList();
        for (Piece p : list) {
            boolean[][] mat = p.possibleMoves();
            for (int i = 0; i < board.getRows(); i++) {
                for (int j = 0; j < board.getCols(); j++) {
                    if (mat[i][j]) {
                        Position source = ((ChessPiece) p).getChessPosition().toPosition();
                        Position target = new Position(i, j);
                        Piece captured = makeMove(source, target);
                        boolean test = testCheck(color);
                        undoMove(source, target, captured);

                        if (!test) {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }

    /*@ private normal_behavior
      @   requires piece != null;
      @   requires col >= 'a' && col <= 'h';
      @   requires row >= 1 && row <= 8;
      @   assignable board, piecesOnTheBoard;
      @*/
    private void placeNewPiece(char col, int row, ChessPiece piece) {
        board.placePiece(piece, new ChessPosition(row, col).toPosition());
        piecesOnTheBoard.add(piece);
    }

    /*@ private normal_behavior
      @   assignable board, piecesOnTheBoard;
      @*/
    private void initialSetup() {
        placeNewPiece('a', 1, new Rook(board, Color.WHITE));
        placeNewPiece('b', 1, new Knight(board, Color.WHITE));
        placeNewPiece('c', 1, new Bishop(board, Color.WHITE));
        placeNewPiece('d', 1, new Queen(board, Color.WHITE));
        placeNewPiece('e', 1, new King(board, Color.WHITE, this));
        placeNewPiece('f', 1, new Bishop(board, Color.WHITE));
        placeNewPiece('g', 1, new Knight(board, Color.WHITE));
        placeNewPiece('h', 1, new Rook(board, Color.WHITE));
        placeNewPiece('a', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('b', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('c', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('d', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('e', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('f', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('g', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('h', 2, new Pawn(board, Color.WHITE, this));

        placeNewPiece('a', 8, new Rook(board, Color.BLACK));
        placeNewPiece('b', 8, new Knight(board, Color.BLACK));
        placeNewPiece('c', 8, new Bishop(board, Color.BLACK));
        placeNewPiece('d', 8, new Queen(board, Color.BLACK));
        placeNewPiece('e', 8, new King(board, Color.BLACK, this));
        placeNewPiece('f', 8, new Bishop(board, Color.BLACK));
        placeNewPiece('g', 8, new Knight(board, Color.BLACK));
        placeNewPiece('h', 8, new Rook(board, Color.BLACK));
        placeNewPiece('a', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('b', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('c', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('d', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('e', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('f', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('g', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('h', 7, new Pawn(board, Color.BLACK, this));
    }
}
