package chess;

import boardgame.Board;
import boardgame.Piece;
import boardgame.Position;
import chess.pieces.*;

import java.util.ArrayList;
import java.util.List;

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
    //@ spec_public
    private ChessPiece enPassantVulnerable;
    //@ spec_public
    private ChessPiece promoted;
    //@ spec_public
    private final List<Piece> piecesOnTheBoard = new ArrayList<>();
    //@ spec_public
    private final List<Piece> capturedPieces = new ArrayList<>();

    /*@ public normal_behavior
      @   ensures board != null;
      @   ensures board.getRows() == 8 && board.getCols() == 8;
      @   ensures turn == 1;
      @   ensures currentPlayer == Color.WHITE;
      @   ensures check == false;
      @   ensures checkMate == false;
      @   ensures enPassantVulnerable == null;
      @   ensures promoted == null;
      @   ensures piecesOnTheBoard.size() == 32;
      @*/
    public ChessMatch() {
        board = new Board(8, 8);
        turn = 1;
        currentPlayer = Color.WHITE;
        initialSetup();
    }

    /*@ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8; \result[i].length == 8);
      @*/
    public ChessPiece[][] getPieces() {
        ChessPiece[][] mat = new ChessPiece[board.getRows()][board.getCols()];
        for (int i = 0; i < board.getRows(); i++) {
            for (int j = 0; j < board.getCols(); j++) {
                mat[i][j] = (ChessPiece) board.piece(i, j);
            }
        }
        return mat;
    }

    /*@ public normal_behavior
      @   ensures \result == turn;
      @   ensures \result >= 1;
      @   pure
      @*/
    public int getTurn() {
        return turn;
    }

    /*@ public normal_behavior
      @   ensures \result == currentPlayer;
      @   ensures \result != null;
      @   pure
      @*/
    public Color getCurrentPlayer() {
        return currentPlayer;
    }

    /*@ public normal_behavior
      @   ensures \result == check;
      @   pure
      @*/
    public boolean getCheck() {
        return check;
    }

    /*@ public normal_behavior
      @   ensures \result == !checkMate;
      @   pure
      @*/
    public boolean getNotCheckMate() {
        return !checkMate;
    }

    /*@ public normal_behavior
      @   ensures \result == enPassantVulnerable;
      @   pure
      @*/
    public ChessPiece getEnPassantVulnerable() {
        return enPassantVulnerable;
    }

    /*@ public normal_behavior
      @   ensures \result == promoted;
      @   pure
      @*/
    public ChessPiece getPromoted() {
        return promoted;
    }

    /*@ public normal_behavior
      @   requires sourcePos != null;
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8; \result[i].length == 8);
      @ also public exceptional_behavior
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
      @   assignable board, turn, currentPlayer, check, checkMate,
      @              enPassantVulnerable, promoted, piecesOnTheBoard, capturedPieces;
      @ also public exceptional_behavior
      @   requires sourcePos != null && targetPos != null;
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
            if (moved.getColor() == Color.WHITE && target.getRow() == 0 || moved.getColor() == Color.BLACK && target.getRow() == 7) {
                promoted = (ChessPiece) board.piece(target);
                promoted = replacePromotedPiece("Q");
            }
        }

        check = (testCheck(opponent(currentPlayer)));
        if (testCheckMate(opponent(currentPlayer))) {
            checkMate = true;
        } else {
            nextTurn();
        }

        // En Passant
        if (moved instanceof Pawn && (target.getRow() == source.getRow() - 2 || target.getRow() == source.getRow() + 2)) {
            enPassantVulnerable = moved;
        } else {
            enPassantVulnerable = null;
        }

        return (ChessPiece) captured;
    }

    /*@ public normal_behavior
      @   requires type != null;
      @   requires promoted != null;
      @   requires type.equals("B") || type.equals("N") || type.equals("R") || type.equals("Q");
      @   ensures \result != null;
      @   assignable board, piecesOnTheBoard, promoted;
      @ also public normal_behavior
      @   requires type != null;
      @   requires promoted != null;
      @   requires !type.equals("B") && !type.equals("N") && !type.equals("R") && !type.equals("Q");
      @   ensures \result == \old(promoted);
      @ also public exceptional_behavior
      @   requires promoted == null;
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
        return newPiece;
    }

    /*@ private normal_behavior
      @   requires type != null;
      @   requires color != null;
      @   requires type.equals("B") || type.equals("N") || type.equals("Q") || type.equals("R");
      @   ensures \result != null;
      @   ensures type.equals("B") ==> \result instanceof Bishop;
      @   ensures type.equals("N") ==> \result instanceof Knight;
      @   ensures type.equals("Q") ==> \result instanceof Queen;
      @   ensures type.equals("R") ==> \result instanceof Rook;
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
                Position pawnPosition = new Position(p.getColor() == Color.WHITE ? target.getRow() + 1 : target.getRow() - 1, target.getCol());
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
                Position pawnPosition = new Position(p.getColor() == Color.WHITE ? 3 : 4, target.getCol());
                board.placePiece(pawn, pawnPosition);
            }
        }

        capturedPieces.remove(captured);
        piecesOnTheBoard.add(captured);
    }

    /*@ private normal_behavior
      @   requires pos != null;
      @ also private exceptional_behavior
      @   requires pos != null;
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
      @ also private exceptional_behavior
      @   requires source != null && target != null;
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
      @   ensures currentPlayer != \old(currentPlayer);
      @   assignable turn, currentPlayer;
      @*/
    private void nextTurn() {
        turn++;
        currentPlayer = (currentPlayer == Color.WHITE) ? Color.BLACK : Color.WHITE;
    }

    /*@ private normal_behavior
      @   requires color != null;
      @   ensures \result != null;
      @   ensures \result != color;
      @   ensures color == Color.WHITE ==> \result == Color.BLACK;
      @   ensures color == Color.BLACK ==> \result == Color.WHITE;
      @   pure
      @*/
    private Color opponent(Color color) {
        return color == Color.WHITE ? Color.BLACK : Color.WHITE;
    }

    /*@ private normal_behavior
      @   requires color != null;
      @   ensures \result != null;
      @   ensures \result instanceof King;
      @ also private exceptional_behavior
      @   requires color != null;
      @   signals_only IllegalStateException;
      @*/
    private ChessPiece king(Color color) {
        List<Piece> list = piecesOnTheBoard.stream().filter(x -> x != null && ((ChessPiece) x).getColor() == color).toList();
        for (Piece p : list) {
            if (p instanceof King) {
                return (ChessPiece) p;
            }
        }
        throw new IllegalStateException("Não existe um rei " + color + " no tabuleiro.");
    }

    /*@ private normal_behavior
      @   requires color != null;
      @*/
    private boolean testCheck(Color color) {
        Position kingPos = king(color).getChessPosition().toPosition();
        List<Piece> opponentPieces = piecesOnTheBoard.stream().filter(x -> x != null && ((ChessPiece) x).getColor() == opponent(color)).toList();
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
      @*/
    private boolean testCheckMate(Color color) {
        if (!testCheck(color)) return false;

        List<Piece> list = piecesOnTheBoard.stream().filter(x -> x != null && ((ChessPiece) x).getColor() == color).toList();
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
      @   ensures piecesOnTheBoard.contains(piece);
      @   ensures piecesOnTheBoard.size() == \old(piecesOnTheBoard.size()) + 1;
      @   assignable board, piecesOnTheBoard;
      @*/
    private void placeNewPiece(char col, int row, ChessPiece piece) {
        board.placePiece(piece, new ChessPosition(row, col).toPosition());
        piecesOnTheBoard.add(piece);
    }

    /*@ private normal_behavior
      @   ensures piecesOnTheBoard.size() == 32;
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
