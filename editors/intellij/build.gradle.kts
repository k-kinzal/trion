import org.jetbrains.intellij.platform.gradle.IntelliJPlatformType
import org.jetbrains.intellij.platform.gradle.TestFrameworkType
import org.jetbrains.kotlin.gradle.dsl.JvmTarget
import org.jetbrains.kotlin.gradle.dsl.KotlinVersion

plugins {
    id("org.jetbrains.kotlin.jvm") version "2.4.21"
    id("org.jetbrains.intellij.platform") version "2.20.0"
}

group = "dev.trion"
version = "0.3.0"

repositories {
    mavenCentral()
    intellijPlatform {
        defaultRepositories()
    }
}

dependencies {
    intellijPlatform {
        intellijIdeaCommunity("2024.3.6")
        plugin("com.redhat.devtools.lsp4ij", "0.21.0")
        pluginVerifier()
        testFramework(TestFrameworkType.Platform)
    }
    testImplementation("junit:junit:4.13.2")
    testImplementation("org.opentest4j:opentest4j:1.3.0")
}

java {
    sourceCompatibility = JavaVersion.VERSION_21
    targetCompatibility = JavaVersion.VERSION_21
}

kotlin {
    compilerOptions {
        jvmTarget = JvmTarget.JVM_21
        // The oldest supported IDE, 2024.3, ships the Kotlin 2.0 standard library.
        apiVersion = KotlinVersion.KOTLIN_2_0
    }
}

intellijPlatform {
    // The single settings page has nothing worth indexing, and this step launches an IDE.
    buildSearchableOptions = false
    pluginConfiguration {
        ideaVersion {
            sinceBuild = "243"
            untilBuild = provider { null }
        }
    }
    pluginVerification {
        ides {
            create(IntelliJPlatformType.IntellijIdeaCommunity, "2024.3.6")
            create(IntelliJPlatformType.IntellijIdeaCommunity, "2025.2.6.4")
            // The IDE on this machine, when it is installed: a build where the browser is a plugin.
            file("/Applications/RustRover.app").takeIf { it.exists() }?.let { local(it.absolutePath) }
        }
    }
}
