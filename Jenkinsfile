pipeline {
  agent {
    dockerfile {
      label 'docker && !smol'
      additionalBuildArgs '--build-arg K_COMMIT="$(cd deps/k && git rev-parse --short=7 HEAD)" --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  environment {
    GITHUB_TOKEN = credentials('rv-jenkins')
    VERSION      = '1.0.0'
    K_VERSION    = '5.0.0'
    K_ROOT_URL   = 'https://github.com/kframework/k/releases/download'
    PACKAGE      = 'kevm'
    ROOT_URL     = 'https://github.com/kframework/evm-semantics/releases/download'
    LONG_REV     = """${sh(returnStdout: true, script: 'git rev-parse HEAD').trim()}"""
  }
  options { ansiColor('xterm') }
  stages {
    stage('Init title') {
      when { changeRequest() }
      steps { script { currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}" } }
    }
    stage('Build and Test') {
      stages {
        stage('Deps')  { steps { sh 'make plugin-deps'            } }
        stage('Build') { steps { sh 'make build RELEASE=true -j6' } }
        stage('Test Execution') {
          failFast true
          options { timeout(time: 25, unit: 'MINUTES') }
          parallel {
            stage('Conformance (LLVM)') { steps { sh 'make test-conformance -j8 TEST_CONCRETE_BACKEND=llvm' } }
            stage('VM (Haskell)')       { steps { sh 'make test-vm -j8 TEST_CONCRETE_BACKEND=haskell'       } }
          }
        }
        stage('Proofs') {
          options {
            lock("proofs-${env.NODE_NAME}")
            timeout(time: 80, unit: 'MINUTES')
          }
          parallel {
            stage('Java')              { steps { sh 'make test-prove -j5 TEST_SYMBOLIC_BACKEND=java'    } }
            stage('Haskell')           { steps { sh 'make test-prove -j4 TEST_SYMBOLIC_BACKEND=haskell' } }
            stage('Haskell (dry-run)') { steps { sh 'make test-haskell-dry-run -j3'                     } }
          }
        }
        stage('Test Lemmas') {
          options { timeout(time: 10, unit: 'MINUTES') }
          stages {
            stage('Generate Obligations')  { steps { sh 'make tests/specs/lemmas.k.gen-proofs'                     } }
            stage('Discharge Obligations') { steps { sh 'make test-prove-lemmas -j6 TEST_SYMBOLIC_BACKEND=haskell' } }
          }
        }
        stage('Test Interactive') {
          failFast true
          options { timeout(time: 35, unit: 'MINUTES') }
          parallel {
            stage('LLVM krun')      { steps { sh 'make test-interactive-run TEST_CONCRETE_BACKEND=llvm'           } }
            stage('Java krun')      { steps { sh 'make test-interactive-run TEST_CONCRETE_BACKEND=java'           } }
            stage('Haskell krun')   { steps { sh 'make test-interactive-run TEST_CONCRETE_BACKEND=haskell'        } }
            stage('LLVM Kast')      { steps { sh 'make test-parse TEST_CONCRETE_BACKEND=llvm'                     } }
            stage('Failing tests')  { steps { sh 'make test-failure TEST_CONCRETE_BACKEND=llvm'                   } }
            stage('Java KLab')      { steps { sh 'make test-klab-prove TEST_SYMBOLIC_BACKEND=java'                } }
            stage('Haskell Search') { steps { sh 'make test-interactive-search TEST_SYMBOLIC_BACKEND=haskell -j4' } }
            stage('KEVM help')      { steps { sh './kevm help'                                                    } }
          }
        }
      }
    }
    stage('Deploy') {
      when {
        branch 'master'
        beforeAgent true
      }
      stages {
        stage('Update Dependents') {
          steps {
            build job: 'rv-devops/master', propagate: false, wait: false                                         \
                , parameters: [ booleanParam ( name: 'UPDATE_DEPS'         , value: true                       ) \
                              , string       ( name: 'UPDATE_DEPS_REPO'    , value: 'kframework/evm-semantics' ) \
                              , string       ( name: 'UPDATE_DEPS_VERSION' , value: "${env.LONG_REV}")           \
                              ]
          }
        }
        stage('Jello Paper') {
          steps {
            sshagent(['2b3d8d6b-0855-4b59-864a-6b3ddf9c9d1a']) {
              dir("kevm-${env.VERSION}-jello-paper") {
                sh '''
                  git clone 'ssh://github.com/kframework/evm-semantics.git'
                  cd evm-semantics
                  git checkout -B gh-pages origin/master
                  rm -rf .build .gitignore .gitmodules cmake deps Dockerfile Jenkinsfile kast-json.py kevm kore-json.py LICENSE Makefile media package
                  git add ./
                  git commit -m 'gh-pages: remove unrelated content'
                  git fetch origin gh-pages
                  git merge --strategy ours FETCH_HEAD
                  git push origin gh-pages
                '''
              }
            }
          }
        }
      }
    }
  }
}
