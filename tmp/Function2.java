package lang.function;

@FunctionalInterface
public interface Function2<A, B, R> {
  R apply2(A arg1, B arg2);
}
