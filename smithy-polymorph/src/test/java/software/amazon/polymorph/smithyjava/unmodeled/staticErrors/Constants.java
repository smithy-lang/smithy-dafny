package software.amazon.polymorph.smithyjava.unmodeled.staticErrors;

class Constants {
    static String NATIVE_ERROR_EXPECTED = """
            package software.amazon.cryptography.model;
            public class NativeError extends RuntimeException {
              protected NativeError(BuilderImpl builder) {
                super(messageFromBuilder(builder), builder.cause());
              }
              public static Builder builder() {return new BuilderImpl();}
              public Builder toBuilder() {return new BuilderImpl(this);}
              private static String messageFromBuilder(Builder builder) {
                if (builder.message() != null) {
                  return builder.message();
                }
                if (builder.cause() != null) {
                  return builder.cause().getMessage();
                }
                return null;
              }
              public String message() {
                return this.getMessage();
              }
              public Throwable cause() {
                return this.getCause();
              }
              static class BuilderImpl implements Builder {
                protected String message;
                protected Throwable cause;
                protected BuilderImpl() {}
                protected BuilderImpl(NativeError model) {
                  this.cause = model.getCause();
                  this.message = model.getMessage();
                }
                public Builder message(String message) {
                  this.message = message;
                  return this;
                }
                public String message() {return this.message;}
                public Builder cause(Throwable cause) {
                  this.cause = cause;
                  return this;
                }
                public Throwable cause() {return this.cause;}
                public NativeError build() {return new NativeError(this);}
              }
              public interface Builder {
                Builder message(String message);
                String message();
                Builder cause(Throwable cause);
                Throwable cause();
                NativeError build();
              }
            }""";

    static String OPAQUE_ERROR_EXPECTED = """
            package software.amazon.cryptography.model;
            public class OpaqueError extends NativeError {
              private final Object obj;
              protected OpaqueError(BuilderImpl builder) {
                super(builder);
                this.obj = builder.obj();
              }
              @Override
              public Builder toBuilder() {return new BuilderImpl(this);}
              public static Builder builder() {return new BuilderImpl();}
              public Object obj() {return this.obj;}
              public interface Builder extends NativeError.Builder {
                Builder message(String message);
                Builder cause(Throwable cause);
                Builder obj(Object obj);
                Object obj();
                OpaqueError build();
              }
              static class BuilderImpl extends NativeError.BuilderImpl implements Builder {
                protected Object obj;
                protected BuilderImpl() {}
                protected BuilderImpl(OpaqueError model) {
                  super(model);
                  this.obj = model.obj();
                }
                public Builder obj(Object obj) {
                  this.obj = obj;
                  return this;
                }
                public Object obj() {return this.obj;}
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
                public OpaqueError build() {return new OpaqueError(this);}
              }
            }""";

    static String COLLECTION_ERROR_EXPECTED = """
            package software.amazon.cryptography.model;
            import java.util.List;
            public class CollectionOfErrors extends NativeError {
              private final List<NativeError> list;
              protected CollectionOfErrors(BuilderImpl builder) {
                super(builder);
                this.list = builder.list();
              }
              public List<NativeError> list() {return this.list;}
              @Override
              public Builder toBuilder() {return new BuilderImpl(this);}
              public static Builder builder() {return new BuilderImpl();}
              public interface Builder extends NativeError.Builder {
                Builder message(String message);
                Builder cause(Throwable cause);
                Builder list(List<NativeError> list);
                List<NativeError> list();
                CollectionOfErrors build();
              }
              static class BuilderImpl extends NativeError.BuilderImpl implements Builder {
                protected List<NativeError> list;
                protected BuilderImpl() {}
                protected BuilderImpl(CollectionOfErrors model) {
                  super(model);
                  this.list = model.list();
                }
                public Builder list(List<NativeError> list) {
                  this.list = list;
                  return this;
                }
                public List<NativeError> list() {return this.list;}
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
                public CollectionOfErrors build() {return new CollectionOfErrors(this);}
              }
            }
            """;
}
