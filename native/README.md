# Native Datalevin

Datalevin can be compiled as a GraalVM native image.

## Build Native Datalevin

Assuming that you can build JVM Datalevin already, i.e. you have
[JDK](https://openjdk.java.net/) and [lein](https://leiningen.org/), here are
the steps to build native Datalevin binary on your platform.

### Linux/MacOS

1. [Install GraalVM](https://www.graalvm.org/docs/getting-started/#install-graalvm)
2. [Intsall GraalVM native image](https://www.graalvm.org/reference-manual/native-image/)
3. Run `script/compile`.

If the compilation is successful, two binaries will appear in this directory:
`dtlv ` and `dtlv-test`. The former is the Datalevin command line shell, and the
latter runs all the Datalevin tests in native mode. These are standalone
executable that you can immediately run.

### Windows

Same as the above, except to run `script/compile.bat` instead in step 3.

If the build is successful, you will get `dtlv.exe` and `dtlv-test.exe`.


## Compiling Datalevin Dependency to Native Image

If your application depends on Datalevin library, and you want to compile your
application into a GraalVM native image, you need to use `org.clojars.huahaiy/datalevin-native` as the dependency, instead of `datalevin/datalevin`.

`datalevin-native` includes [GraalVM specific native
code](https://yyhh.org/blog/2021/02/writing-c-code-in-javaclojure-graalvm-specific-programming/)
that are pre-compiled for various platforms.

Like all Clojure applications, class initialization needs to be done at [native image
build time](https://github.com/clj-easy/graal-docs#class-initialization),
otherwise, native image build will fail due to link errors. During the native
image build time, our class initialization code extracts native libraries from
the `datalevin-native` jar and put them in the GraalVM's default `CLibraryPath`
for the platform (e.g. `${GRAALVM_HOME}/lib/svm/clibraries/linux-amd64/`). The
files will be deleted on JVM exit.

If you are uncomfortable with writing the default location or lack the write
permission for that directory, you can set an environment variable
`DTLV_LIB_EXTRACT_DIR` in the shell doing the native image build, and the native
libraries will then be put there instead. If so, you must also add
`-H:CLibraryPath=${DTLV_LIB_EXTRACT_DIR}` option in your native image build command
line. The directory referred to by the environment variable must exist and is
writable.

Once built, Datalevin's native dependencies are linked into your image statically.

For CI/CD, you may want to consult our [Github
Action](https://github.com/juji-io/datalevin/blob/master/.github/workflows/release.binaries.yml)
(for Linux/MacOS) and
[Appveoyor](https://github.com/juji-io/datalevin/blob/master/appveyor.yml) (for
Windows) yaml files for examples.
