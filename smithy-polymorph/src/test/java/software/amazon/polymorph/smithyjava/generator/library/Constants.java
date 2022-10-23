package software.amazon.polymorph.smithyjava.generator.library;

class Constants {
    static String TEST_ERROR_EXPECTED = """
            package software.amazon.cryptography.test.model;
                        
            public class TestError extends NativeError {
              protected TestError(BuilderImpl builder) {
                super(builder);
              }
                        
              @Override
              public Builder toBuilder() {
                return new BuilderImpl(this);
              }
                        
              public static Builder builder() {
                return new BuilderImpl();
              }
                        
              interface Builder extends NativeError.Builder {
                Builder message(String message);
                        
                Builder cause(Throwable cause);
                        
                TestError build();
              }
                        
              protected static class BuilderImpl extends NativeError.BuilderImpl implements Builder {
                protected BuilderImpl() {
                }
                        
                protected BuilderImpl(TestError model) {
                  super(model);
                }
                        
                @Override
                public Builder message(String message) {
                  super.message(message);
                  return this;
                }
                        
                @Override
                public Builder cause(Throwable cause) {
                  super.cause(cause);
                  return this;
                }
                        
                @Override
                public TestError build() {
                  if (this.message() == null)  {
                    throw new IllegalArgumentException("Missing value for required field `message`");
                  }
                  return new TestError(this);
                }
              }
            }
            """;
}
