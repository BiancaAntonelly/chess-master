package app;

import java.util.Arrays;
import java.util.InputMismatchException;
import java.util.List;
import java.util.Scanner;

import chess.ChessMatch;
import chess.ChessPiece;
import chess.ChessPosition;
import chess.Color;

public class UI {

    public static final String ANSI_RESET = "\u001B[0m";
    public static final String ANSI_YELLOW = "\u001B[33m";
    public static final String ANSI_WHITE = "\u001B[37m";
    public static final String ANSI_BLUE_BACKGROUND = "\u001B[44m";

    /*@ public normal_behavior
      @   assignable \everything;
      @*/
    public static void clearScreen() {
        System.out.print("\033[H\033[2J");
        System.out.flush();
    }

    /*@ public behavior
      @   requires sc != null;
      @   assignable \everything;
      @   ensures \result != null;
      @   signals (InputMismatchException e) true;
      @*/
    public static ChessPosition readChessPosition(Scanner sc) {
        try {
            String s = sc.nextLine();
            char column = s.charAt(0);
            int row = Integer.parseInt(s.substring(1));
            return new ChessPosition(row, column);
        } catch (RuntimeException e) {
            throw new InputMismatchException("Posição inválida. Valores válidos estão entre a1 e h8.");
        }
    }

    /*@ public normal_behavior
      @   requires chessMatch != null;
      @   requires captured != null;
      @   // cada peça capturada é um ChessPiece bem formado (invariantes de Piece/ChessPiece)
      @   requires (\forall int i; 0 <= i && i < captured.size();
      @                captured.get(i) != null
      @             && captured.get(i).modelBoard != null
      @             && (captured.get(i).modelPosition == null
      @                 || (captured.get(i).modelPosition.getRow() >= 0
      @                     && captured.get(i).modelPosition.getRow() < 8
      @                     && captured.get(i).modelPosition.getCol() >= 0
      @                     && captured.get(i).modelPosition.getCol() < 8))
      @             && captured.get(i).color != null
      @             && captured.get(i).moveCount >= 0);
      @   assignable \everything;
      @*/
    public static void printMatch(ChessMatch chessMatch, List<ChessPiece> captured) {
        printBoard(chessMatch.getPieces());
        System.out.println();
        printCapturedPieces(captured);
        System.out.println();
        System.out.println("Turno : " + chessMatch.getTurn());
        if (chessMatch.getNotCheckMate()) {
            System.out.println("Aguardando jogador: " + chessMatch.getCurrentPlayer());
            if (chessMatch.getCheck()) {
                System.out.println("XEQUE!");
            }
        } else {
            System.out.println("XEQUE-MATE!");
            System.out.println("Vencedor: " + chessMatch.getCurrentPlayer());
        }
    }

    /*@ public behavior
      @   requires pieces != null;
      @   // tabuleiro de xadrez: no máximo 8 linhas
      @   requires 0 < pieces.length && pieces.length <= 8;
      @   requires (\forall int i; 0 <= i && i < pieces.length; pieces[i] != null);
      @   assignable \everything;
      @*/
    public static void printBoard(ChessPiece[][] pieces) {
        /*@ loop_invariant 0 <= i && i <= pieces.length;
          @ loop_invariant pieces.length <= 8;
          @ decreases pieces.length - i;
          @*/
        for (int i = 0; i < pieces.length; i++) {
            System.out.print((8 - i) + " ");
            /*@ loop_invariant 0 <= j && j <= pieces[i].length;
              @ decreases pieces[i].length - j;
              @*/
            for (int j = 0; j < pieces[i].length; j++) {
                printPiece(pieces[i][j], false);
            }
            System.out.println();
        }
        System.out.println("  a b c d e f g h");
    }

    /*@ public behavior
      @   requires pieces != null && possibleMoves != null;
      @   // tabuleiro de xadrez: no máximo 8 linhas
      @   requires 0 < pieces.length && pieces.length <= 8;
      @   requires pieces.length == possibleMoves.length;
      @   requires (\forall int i; 0 <= i && i < pieces.length;
      @               pieces[i] != null && possibleMoves[i] != null &&
      @               pieces[i].length == possibleMoves[i].length);
      @   assignable \everything;
      @*/
    public static void printBoard(ChessPiece[][] pieces, boolean[][] possibleMoves) {
        /*@ loop_invariant 0 <= i && i <= pieces.length;
          @ loop_invariant pieces.length <= 8;
          @ decreases pieces.length - i;
          @*/
        for (int i = 0; i < pieces.length; i++) {
            System.out.print((8 - i) + " ");
            /*@ loop_invariant 0 <= j && j <= pieces[i].length;
              @ decreases pieces[i].length - j;
              @*/
            for (int j = 0; j < pieces[i].length; j++) {
                printPiece(pieces[i][j], possibleMoves[i][j]);
            }
            System.out.println();
        }
        System.out.println("  a b c d e f g h");
    }

    /*@ helper @*/
    private static void printPiece(/*@ nullable @*/ ChessPiece piece, boolean background) {
        if (background) {
            System.out.print(ANSI_BLUE_BACKGROUND);
        }
        if (piece == null) {
            System.out.print("-" + ANSI_RESET);
        } else {
            if (piece.getColor() == Color.WHITE) {
                System.out.print(ANSI_WHITE + piece + ANSI_RESET);
            } else {
                System.out.print(ANSI_YELLOW + piece + ANSI_RESET);
            }
        }
        System.out.print(" ");
    }

    /*@ requires captured != null;
      @ assignable \everything;
      @*/
    private static void printCapturedPieces(List<ChessPiece> captured) {
        List<ChessPiece> white = new java.util.ArrayList<>();
        List<ChessPiece> black = new java.util.ArrayList<>();

        for (int i = 0; i < captured.size(); i++) {
            ChessPiece piece = captured.get(i);
            if (piece != null) {
                if (piece.getColor() == Color.WHITE) {
                    white.add(piece);
                } else if (piece.getColor() == Color.BLACK) {
                    black.add(piece);
                }
            }
        }

        System.out.println("Peças capturadas:");
        System.out.print("Brancas: ");
        System.out.print(ANSI_WHITE);
        System.out.println(Arrays.toString(white.toArray()));
        System.out.print(ANSI_RESET);
        System.out.print("Pretas: ");
        System.out.print(ANSI_YELLOW);
        System.out.println(Arrays.toString(black.toArray()));
        System.out.print(ANSI_RESET);
    }

}
